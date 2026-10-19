-- Prove2me | solution 1 for DusartCert.run_18
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-10-16T20:45:41.044975+00:00
-- url     : https://prove2.me/submissions/d97128f9-5cbc-41fb-95ab-b86f3b9ba89a

import Definitions.Def_DusartCertData_18

theorem solution :
    DusartCert.run (2 ^ 64) 4823768287920834435 DusartCert.Gen.items18 (2748587, 24, 32867759843802371053, 295192120209138332, 2731087) =
    some (2896253, 32, 32932796737298880252, 295192131736596007, 2896253) := by
  decide +kernel
