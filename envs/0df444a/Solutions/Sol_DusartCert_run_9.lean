-- Prove2me | solution 1 for DusartCert.run_9
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-10-16T20:45:27.217668+00:00
-- url     : https://prove2.me/submissions/7954cfe0-8efe-4d18-ac26-207f875b6e1e

import Definitions.Def_DusartCertData_9

theorem solution :
    DusartCert.run (2 ^ 64) 4823768287920834435 DusartCert.Gen.items9 (1389643, 17, 31999319086394615890, 295191893083160260, 1389643) =
    some (1543631, 29, 32135949121031599169, 295191939756728298, 1543631) := by
  decide +kernel
