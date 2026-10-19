-- Prove2me | solution 1 for DusartCert.run_2
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-10-16T20:45:18.426997+00:00
-- url     : https://prove2.me/submissions/e5791e07-9423-4eef-9ea0-b0685df8050a

import Definitions.Def_DusartCertData_2

theorem solution :
    DusartCert.run (2 ^ 64) 4823768287920834435 DusartCert.Gen.items2 (313909, 38, 29949838536048777621, 295190170988520029, 313909) =
    some (471407, 37, 30533283633238984754, 295190935812865561, 471407) := by
  decide +kernel
