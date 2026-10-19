-- Prove2me | solution 1 for DusartCert.run_4
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-10-16T20:45:19.957978+00:00
-- url     : https://prove2.me/submissions/9d68ec41-60c1-4d8e-afeb-84136ec2e0b4

import Definitions.Def_DusartCertData_4

theorem solution :
    DusartCert.run (2 ^ 64) 4823768287920834435 DusartCert.Gen.items4 (627089, 6, 30932256325294171710, 295191304195099104, 627089) =
    some (783151, 14, 31236217629858793834, 295191521532773423, 783151) := by
  decide +kernel
