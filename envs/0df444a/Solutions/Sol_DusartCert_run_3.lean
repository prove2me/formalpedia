-- Prove2me | solution 1 for DusartCert.run_3
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-10-16T20:45:19.137072+00:00
-- url     : https://prove2.me/submissions/349b2da2-fd87-48aa-bc91-0c0be19dab5d

import Definitions.Def_DusartCertData_3

theorem solution :
    DusartCert.run (2 ^ 64) 4823768287920834435 DusartCert.Gen.items3 (471407, 37, 30533283633238984754, 295190935812865561, 471407) =
    some (627089, 6, 30932256325294171710, 295191304195099104, 627089) := by
  decide +kernel
