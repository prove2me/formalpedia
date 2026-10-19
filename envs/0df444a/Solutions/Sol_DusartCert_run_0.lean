-- Prove2me | solution 1 for DusartCert.run_0
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-10-16T20:45:10.640994+00:00
-- url     : https://prove2.me/submissions/ac35b4c6-1082-41ef-8970-3635a7391cfa

import Definitions.Def_DusartCertData_0

theorem solution :
    DusartCert.run (2 ^ 64) 4823768287920834435 DusartCert.Gen.items0 (11, 1, 0, 0, 10372) =
    some (157007, 30, 28914026580724975665, 295187783405350399, 157007) := by
  decide +kernel
