-- Prove2me | solution 1 for DusartCert.run_6
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-10-16T20:45:21.841912+00:00
-- url     : https://prove2.me/submissions/6864a4db-7fa1-4fe7-89ad-127309fd1a9d

import Definitions.Def_DusartCertData_6

theorem solution :
    DusartCert.run (2 ^ 64) 4823768287920834435 DusartCert.Gen.items6 (938879, 40, 31481351364166126527, 295191664710676337, 938879) =
    some (1089523, 10, 31678971880380322602, 295191762507451599, 1089523) := by
  decide +kernel
