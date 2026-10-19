-- Prove2me | solution 1 for DusartCert.run_17
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-10-16T20:45:38.980108+00:00
-- url     : https://prove2.me/submissions/1f8c36a9-5c62-46bf-bd5f-2dfe908bf23e

import Definitions.Def_DusartCertData_17

theorem solution :
    DusartCert.run (2 ^ 64) 4823768287920834435 DusartCert.Gen.items17 (2592589, 31, 32794939795817715799, 295192106567167876, 2592589) =
    some (2748587, 24, 32867759843802371053, 295192120209138332, 2731087) := by
  decide +kernel
