-- Prove2me | solution 1 for DusartCert.run_8
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-10-16T20:45:23.97831+00:00
-- url     : https://prove2.me/submissions/0d7caae7-2c1e-4986-bf8d-5f0a093e7af9

import Definitions.Def_DusartCertData_8

theorem solution :
    DusartCert.run (2 ^ 64) 4823768287920834435 DusartCert.Gen.items8 (1239877, 8, 31850028783494702718, 295191836174878117, 1239877) =
    some (1389643, 17, 31999319086394615890, 295191893083160260, 1389643) := by
  decide +kernel
