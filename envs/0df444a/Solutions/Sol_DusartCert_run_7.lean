-- Prove2me | solution 1 for DusartCert.run_7
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-10-16T20:45:22.730983+00:00
-- url     : https://prove2.me/submissions/cf357f30-4f9e-482d-883e-c811f01755e6

import Definitions.Def_DusartCertData_7

theorem solution :
    DusartCert.run (2 ^ 64) 4823768287920834435 DusartCert.Gen.items7 (1089523, 10, 31678971880380322602, 295191762507451599, 1089523) =
    some (1239877, 8, 31850028783494702718, 295191836174878117, 1239877) := by
  decide +kernel
