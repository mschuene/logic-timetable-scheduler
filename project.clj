(defproject logic-timetable-scheduler "0.1.0-SNAPSHOT"
  :description "FIXME: write description"
  :url "http://example.com/FIXME"
  :license {:name "Eclipse Public License"
            :url "http://www.eclipse.org/legal/epl-v10.html"}
  :jvm-opts ["-Xmx4g" "-server" "-Xss1g"]
  :dependencies [[org.clojure/clojure "1.6.0"]
                 [org.clojure/tools.trace "0.7.8"]
                 [clocop "0.2.0"]]
  :aot :all
  :main logic-timetable-scheduler.core)
