(ns logic-timetable-scheduler.core
  (:require [clojure.core.logic :as l]
            [clocop.core :as c]
            [logic-timetable-scheduler.cardinality :refer :all]
            [clocop.constraints :as constr
             :refer [$= $+ $reify $and $<= $if $!= $>= $or $iff]])
  (:gen-class))

(def teachers [{:sid "Kk" :hours-per-week 15}
               {:sid "sch" :hours-per-week 9}
               {:sid "ss" :hours-per-week 15}
               {:sid "ww" :hours-per-week 15}])

(def rooms [{:name "A1"}
            {:name "A2"}
            {:name "A3"}
            {:name "A4"}
            {:name "Sporthalle"}])

(def classes [{:name "3a" :teacher (first teachers) :needed-subjects {"Deutsch" 3 "Mathe" 4 "Sport" 2 "Kunst" 2 "Sachkunde" 4} :room (first rooms)}
              {:name "3b" :teacher (first teachers) :needed-subjects {"Deutsch" 3 "Mathe" 4 "Sport" 2 "Kunst" 2 "Sachkunde" 4} :room (first rooms)}
              {:name "3c" :teacher (first teachers) :needed-subjects {"Deutsch" 3 "Mathe" 4 "Sport" 2 "Kunst" 2 "Sachkunde" 4} :room (first rooms)}
              {:name "3d" :teacher (first teachers) :needed-subjects {"Deutsch" 3 "Mathe" 4 "Sport" 2 "Kunst" 2 "Sachkunde" 4} :room (first rooms)}
              {:name "1a" :teacher (last teachers) :needed-subjects {"Deutsch" 2 "Mathe" 3 "Sport" 2 "Kunst" 2} :room (last rooms)}])


(def days [:monday :tuesday :wednesday :thursday :friday])

(def hours-per-day 100)


(def timeslots
  (for [d days
        h (range 1 (inc hours-per-day))]
    {:day d
     :hour h}))

(def courses
  (for [c classes
        subject (keys (:needed-subjects c))
        numb (range (get (:needed-subjects c) subject))]
    {:class c
     :subject subject
     :number numb}))

(defn encode-literal [name-map literal]
  (if-let [numb (get name-map (:var literal))]
    [name-map (if (:negated? literal) (- numb) numb)]
    (let [mkey (apply max 0 (vals name-map))]
      (prn "literal " literal "not found in name-map")
      (recur (assoc name-map (:var literal) (inc mkey)) literal))))

(defn encode-clause [name-map clause]
  (reduce (fn [[name-map partial-clause] next-literal]
            (let [[name-map encoded-literal]
                  (encode-literal name-map next-literal)]
              [name-map (conj partial-clause encoded-literal)]))
          [name-map []]
          clause))

(defn encode
  "encodes the clauses to dimacs format"
  [clauses]
  (let [[name-map encoded]
        (reduce (fn [[name-map partial-clauses] next-clause]
                  (let [[name-map encoded-clause]
                        (encode-clause name-map next-clause)]
                    [name-map (conj partial-clauses encoded-clause)]))
                [{} []]
                clauses)]
    [name-map
     (apply str "c generated cnf file\n"  "p cnf "
            (count (keys name-map)) " "
            (count encoded) "\n"
            (interpose "\n" (map #(apply str  (concat
                                               (interpose " " %)
                                               " 0"))
                                 encoded)))]))



(comment
  (def as (map (comp gen-var symbol (partial str "a")) (range 8)))
  (def res (at-most as 2))
  (def res (concat start-clauses res))
  (def encoded (encode res))
  encoded
  (spit (str "/home/kima/Downloads/" "cnf1") (second encoded))

  in der shell
  "java -jar sat4j-sat.jar cnf1" im Ordner Downloads
  
  )















































































;;csp zu langsam wie es scheint machen jetzt sat
(comment
  
  ;;how to encode vars
  ;;example ch_{c,h} Fach c wird zur Stunde h unterrichtet

  ;;constraint programming
  ;;welche variablen?
  ;;für jeden  Kurs (also sowas wie 3aMathe1, 3aMathe2, .....)
  ;;eine Variable
  ;;Raum -> index in Raumliste
  ;;Lehrer -> index in Lehrer Liste
  ;;Zeitslot -> index in Zeitslot liste
  (def timetable-store (c/store))
  (def room-vars
    (c/with-store timetable-store
      (->> (for [i (range (count courses))]
             (c/int-var (str "r" i) 0 (dec (count rooms))))
           doall
           (into []))))

  #_(def teaches-vars
      (c/with-store timetable-store
        (->> (for [t (range (count teachers))
                   i (range (count timeslots))]
               (c/int-var (str "teaches" t i) 0 1))
             doall
             (into []))))

  (def teacher-vars
    (c/with-store timetable-store
      (->> (for [i (range (count courses))]
             (c/int-var (str "t" i) 0 (dec (count teachers))))
           doall
           (into []))))

  (def timeslot-vars
    (c/with-store timetable-store
      (->> (for [i (range (count courses))]
             (c/int-var (str "ts" i) 0 (dec (count timeslots))))
           doall
           (into []))))


  (def classes-vars
    (c/with-store timetable-store
      (->> (for [i (range (count courses))]
             (c/int-var (str "c" i) 0 (dec (count classes))))
           doall
           (into []))))

  (def class-course-constraints
    (c/with-store timetable-store
      (->> (for [i (range (count classes))
                 c (range (count courses))]
             (if (= (nth classes i) (:class (nth courses c)))
               ($= i (nth classes-vars c)))))))


  (defn course-at-time-in-room [room time course]
    ($reify ($and ($= (nth timeslot-vars course) time)
                  ($= (nth room-vars course) room))))

  ;;für jeden raum gilt, dass
  ;;für jeden Zeitslot
  ;;nur höchstens ein Kurs, der zu dem Zeitpunkt stattfindet, in dem Raum stattfinden darf
  (def room-clash-constraints
    (c/with-store timetable-store
      (->> (for [r (range (count rooms))
                 i (range (count timeslots))
                 :let [constraints (map (partial course-at-time-in-room r i) (range (count courses)))]]
             (c/constrain! ($<= (apply $+ constraints) 1)))
           doall)))

  (defn teacher-at-time-in-room [teacher time course]
    ($reify ($and ($= (nth timeslot-vars course) time) 
                  ($= (nth teacher-vars course) teacher))))

  ;;für jeden Lehrer gilt, dass
  ;;für jeden Zeitslot
  ;;nur höchstens ein Kurs, der zu dem Zeitpunkt stattfindet, von dem Lehrer unterrichtet werden darf
  (def teacher-clash-constraints
    (c/with-store timetable-store
      (->> (for [t (range (count teachers))
                 i (range (count timeslots))
                 :let [constraints (map (partial teacher-at-time-in-room t i) (range (count courses)))]]
             (c/constrain! ($<= (apply $+ constraints) 1)))
           doall)))

  ;;für jede Klasse gilt, dass
  ;;für jeden Zeitslot
  ;;nur höchstens ein Kurs, der zu dem Zeitpunkt stattfindet, von der Klasse sein darf
  ;;TODO write



  ;;Zeiten von Lehrern verbieten -> sollte machbar sein über für alle Kurse, wenn Kurs k zu Zeit i stattfindet, wobei i eine Sperrzeit von Lehrer x ist, dann ist tk != x
  (def times-not-available
    [[3 6] ;;lehrer 1 nicht erreichbar in Timeslot 3 und 6
     [2 9]]) ;;lehrer 2 nicht in 2 und 9

  (def teacher-not-available-constraints
    (c/with-store timetable-store
      (->> (for [[teacher times] (map-indexed vector times-not-available)
                 time times
                 course (range (count courses))]
             (c/constrain!
              ($if ($= (nth timeslot-vars course) time)
                   ($!= (nth teacher-vars teacher) teacher))))
           doall)))
  ;;maximale und minimale Zeitauslastund eines Lehrers -> reifyen sodass 1 für Lehrer unterrichtet und 0 für nicht , aufaddieren konstrants mit >= und <=
  (def max-min-hours-per-week
    [[10 12] ;;lehrer 1 muss 10 bis 12 Strunden(einschließlich) arbeiten
     [9 13]]) ;;lehrer 2 9 bis 13

  (def max-min-hours-per-week-constraints
    (c/with-store timetable-store
      (->> (for [[teacher [min max]] (map-indexed vector max-min-hours-per-week) 
                 :let [vars
                       (map #($reify ($= (nth teacher-vars %) teacher))
                            (range (count courses)))]]
             (do (c/constrain! ($<= (apply $+ vars) max))
                 (c/constrain! ($>= (apply $+ vars) min))))
           doall)))
  ;;gelbe Zeiten und Bandunterricht -> zur Not special handling außerhalb der anderen Klassen aber sonst nur ein paar weitere constraints
  ;;später

  ;;wegzeiten zwischen gebäuden -> für alle Kurse gilt, sowohl für klasse als auch lehrer, dass für alle anderen Kurse, wenn sie zur Zeit stattfinden, die kleiner als die Wegzeit zwischen den Gebäuden ist, der Lehrer und die Klasse != der des ersten Kurses sein müssen :)
  (def room-to-building
    [:building-1
     :building-1
     :building-1
     :building-1
     :building-2
     :sporthalle])

  (def duration-between-buildings
    {[:building-1 :building-2] 1
     [:building-2 :building-1] 3
     [:building-1 :sporthalle] 3
     [:sporthalle :building-1] 3
     [:building-2 :sporthalle] 3
     [:sporthalle :building-2] 3})


  (def duration-between-buildings-constraints 
    (c/with-store timetable-store
      (->> (for [c (range (count courses))
                 r (range (count rooms))
                 :let [building (room-to-building r)]
                 c2 (range (count courses))
                 :when (not= c c2)
                 r2 (range (count rooms))
                 :let [building2 (room-to-building r2)
                       duration (get duration-between-buildings
                                     [building building2] 0)]
                 :when (> duration 0)
                 d (range duration)]
             (c/constrain! ($if ($or ($= (nth teacher-vars c)
                                         (nth teacher-vars c2))
                                     ($= (nth classes-vars c)
                                         (nth classes-vars c2)))
                                ($!= ($+ (nth timeslot-vars c) d)
                                     (nth timeslot-vars c2)))))
           doall
           (#(prn (count %))))))

  ;;dauer einer Veranstaltung -> für alle anderen Kurse, wenn sie in dem Zeitintervall der Dauer stattfinden gilt, Lehrer Klasse und Raum ungleich den der ersten Veransteltung

  (def duration-of-subject
    {"Sport" 2
     "Kunst" 2})

  (defn duration-of-course [course]
    (get duration-of-subject (:subject course) 1))

  (def duration-of-course-constraints 
    (c/with-store timetable-store
      (->> (for [[i c] (map-indexed vector courses)
                 :let [duration (duration-of-course c)]
                 :when (> duration 1)
                 i2 (range (count courses))
                 :when (not= i i2)
                 d (range 1 duration)]
             (c/constrain! ($if ($or ($= (nth teacher-vars i)
                                         (nth teacher-vars i2))
                                     ($= (nth classes-vars i)
                                         (nth classes-vars i2))
                                     ($= (nth room-vars i)
                                         (nth room-vars i2)))
                                ($!= ($+ (nth timeslot-vars i) d)
                                     (nth timeslot-vars i2)))))
           doall
           (#(prn (count %))))))
  ;;manche Veranstaltungen müssen in bestimmten Räumen stattfinden
  (def needs-certain-room
    {"Sport" 2})

  (def course-room-constraints 
    (c/with-store timetable-store
      (->> (for [[i c] (map-indexed vector courses)
                 :let [room-needed (get needs-certain-room (:subject c))]
                 :when room-needed]
             (c/constrain! ($= (nth room-vars i) room-needed)))
           doall)))


  ;;decodes output into annotated courses with room, teacher and timeslot (and class)
  (defn decode-output [sol]
    (for [[i c] (map-indexed vector courses)
          :let [teacher (nth teachers (get sol (str "t" i)))
                room (nth rooms (get sol (str "r" i)))
                timeslot (nth timeslots (get sol (str "ts" i)))]]
      (assoc c :teacher teacher :room room :timeslot timeslot)))

  (defn by-teacher [courses]
    (group-by :teacher courses))

  (defn by-class [courses]
    (group-by :class courses))

  (defn by-room [courses]
    (group-by :room courses))


  (defn -main  [& args]
    (prn "start with solving")
    
    (prn "solution " (pr-str (c/with-store timetable-store (c/solve! :log? true)))))



  ;;with different search everything looks better :)
  ;;max-regret is best most-constrained also good

  ;;anderes encoding, mehr variablen weniger constraints
  ;;will diistinct benutzen
  ;;(apply distinct room-vars)
  ;;(apply distinct teacher-vars)
  ;;(apply distinct classes-vars)

  ;;dazu muss:
  ;;für jeden Raum variablen, die die Veranstaltungszeitpunkte in ihm
  ;;anzeigen
  ;;für jede Klasse, für jeden Lehrer ....
  ;;lehrer hat unterricht zur zeit x
  ;; <=> kurs x hat unterricht zur Zeit x und Lehrer ist gleich

  )
