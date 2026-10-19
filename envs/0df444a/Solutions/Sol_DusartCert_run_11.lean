-- Prove2me | solution 1 for DusartCert.run_11
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-10-16T20:45:32.616864+00:00
-- url     : https://prove2.me/submissions/266b63d1-bbb9-40aa-8dff-b6b1480f3282

import Definitions.Def_DusartCertData_11

theorem solution :
    DusartCert.run (2 ^ 64) 4823768287920834435 DusartCert.Gen.items11 (1691531, 43, 32253792558277808371, 295191976234856912, 1691531) =
    some (1841113, 10, 32362236360802966132, 295192006970924857, 1841113) := by
  decide +kernel
