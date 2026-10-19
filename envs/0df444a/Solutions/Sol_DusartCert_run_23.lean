-- Prove2me | solution 1 for DusartCert.run_23
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-10-16T20:45:48.401895+00:00
-- url     : https://prove2.me/submissions/46341072-1add-4f96-9b6a-d52fa6ae8f35

import Definitions.Def_DusartCertData_23

theorem solution :
    DusartCert.run (2 ^ 64) 4823768287920834435 DusartCert.Gen.items23 (3499757, 24, 33165865565823600403, 295192168403659644, 3499757) =
    some (3594643, 17, 33198239062610841350, 295192172967369872, 3594643) := by
  decide +kernel
