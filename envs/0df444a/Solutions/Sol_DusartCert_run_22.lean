-- Prove2me | solution 1 for DusartCert.run_22
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-10-16T20:45:47.489619+00:00
-- url     : https://prove2.me/submissions/5ad92a1c-f40d-4b6f-a5d7-d1d360c3698b

import Definitions.Def_DusartCertData_22

theorem solution :
    DusartCert.run (2 ^ 64) 4823768287920834435 DusartCert.Gen.items22 (3352361, 29, 33113334439453082791, 295192160734121521, 3352361) =
    some (3499757, 24, 33165865565823600403, 295192168403659644, 3499757) := by
  decide +kernel
