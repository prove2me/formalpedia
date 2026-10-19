-- Prove2me | solution 1 for DusartCert.run_5
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-10-16T20:45:21.105783+00:00
-- url     : https://prove2.me/submissions/07aa8062-637e-4328-befb-95297b9dd2bd

import Definitions.Def_DusartCertData_5

theorem solution :
    DusartCert.run (2 ^ 64) 4823768287920834435 DusartCert.Gen.items5 (783151, 14, 31236217629858793834, 295191521532773423, 783151) =
    some (938879, 40, 31481351364166126527, 295191664710676337, 938879) := by
  decide +kernel
