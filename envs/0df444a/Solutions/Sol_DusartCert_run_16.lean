-- Prove2me | solution 1 for DusartCert.run_16
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-10-16T20:45:38.271291+00:00
-- url     : https://prove2.me/submissions/05a5123e-a19d-4702-ab9a-bb3db7335f4e

import Definitions.Def_DusartCertData_16

theorem solution :
    DusartCert.run (2 ^ 64) 4823768287920834435 DusartCert.Gen.items16 (2440561, 34, 32719116165820546986, 295192091493095978, 2440561) =
    some (2592589, 31, 32794939795817715799, 295192106567167876, 2592589) := by
  decide +kernel
