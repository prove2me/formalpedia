-- Prove2me | solution 1 for DusartCert.run_10
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-10-16T20:45:29.366509+00:00
-- url     : https://prove2.me/submissions/a4a55d62-b769-461e-ac5b-f154d142ea9f

import Definitions.Def_DusartCertData_10

theorem solution :
    DusartCert.run (2 ^ 64) 4823768287920834435 DusartCert.Gen.items10 (1543631, 29, 32135949121031599169, 295191939756728298, 1543631) =
    some (1691531, 43, 32253792558277808371, 295191976234856912, 1691531) := by
  decide +kernel
