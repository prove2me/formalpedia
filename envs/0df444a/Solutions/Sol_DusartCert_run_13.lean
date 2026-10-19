-- Prove2me | solution 1 for DusartCert.run_13
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-10-16T20:45:35.46173+00:00
-- url     : https://prove2.me/submissions/50135d35-db86-4394-9672-44b08b09f523

import Definitions.Def_DusartCertData_13

theorem solution :
    DusartCert.run (2 ^ 64) 4823768287920834435 DusartCert.Gen.items13 (1998221, 16, 32467007187711904599, 295192034295167718, 1998221) =
    some (2150977, 35, 32560456314796144029, 295192056839835795, 2150977) := by
  decide +kernel
