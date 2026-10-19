-- Prove2me | solution 1 for DusartCert.run_12
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-10-16T20:45:34.683986+00:00
-- url     : https://prove2.me/submissions/f6ae1b49-5b8a-45e1-b11b-ca4f5cdb2c2d

import Definitions.Def_DusartCertData_12

theorem solution :
    DusartCert.run (2 ^ 64) 4823768287920834435 DusartCert.Gen.items12 (1841113, 10, 32362236360802966132, 295192006970924857, 1841113) =
    some (1998221, 16, 32467007187711904599, 295192034295167718, 1998221) := by
  decide +kernel
