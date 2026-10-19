-- Prove2me | solution 1 for DusartCert.run_19
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-10-16T20:45:42.751852+00:00
-- url     : https://prove2.me/submissions/94ac565d-aa4e-4a24-a508-f1061d4a6e1e

import Definitions.Def_DusartCertData_19

theorem solution :
    DusartCert.run (2 ^ 64) 4823768287920834435 DusartCert.Gen.items19 (2896253, 32, 32932796737298880252, 295192131736596007, 2896253) =
    some (3050233, 44, 32996692933121375127, 295192142487132653, 3050233) := by
  decide +kernel
