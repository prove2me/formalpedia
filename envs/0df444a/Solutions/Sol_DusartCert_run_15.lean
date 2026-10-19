-- Prove2me | solution 1 for DusartCert.run_15
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-10-16T20:45:37.318997+00:00
-- url     : https://prove2.me/submissions/29d0461b-856b-445d-981d-70a424776bcf

import Definitions.Def_DusartCertData_15

theorem solution :
    DusartCert.run (2 ^ 64) 4823768287920834435 DusartCert.Gen.items15 (2297887, 15, 32643817001525632203, 295192075592042504, 2297887) =
    some (2440561, 34, 32719116165820546986, 295192091493095978, 2440561) := by
  decide +kernel
