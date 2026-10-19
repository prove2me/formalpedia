-- Prove2me | solution 1 for DusartCert.run_14
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-10-16T20:45:36.547979+00:00
-- url     : https://prove2.me/submissions/fee12eb2-a340-42b7-b744-74a4737d3630

import Definitions.Def_DusartCertData_14

theorem solution :
    DusartCert.run (2 ^ 64) 4823768287920834435 DusartCert.Gen.items14 (2150977, 35, 32560456314796144029, 295192056839835795, 2150977) =
    some (2297887, 15, 32643817001525632203, 295192075592042504, 2297887) := by
  decide +kernel
