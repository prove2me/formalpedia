-- Prove2me | solution 1 for DusartCert.run_1
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-10-16T20:45:14.515983+00:00
-- url     : https://prove2.me/submissions/f089a637-4b70-43bf-a3cd-0b917caa58a4

import Definitions.Def_DusartCertData_1

theorem solution :
    DusartCert.run (2 ^ 64) 4823768287920834435 DusartCert.Gen.items1 (157007, 30, 28914026580724975665, 295187783405350399, 157007) =
    some (313909, 38, 29949838536048777621, 295190170988520029, 313909) := by
  decide +kernel
