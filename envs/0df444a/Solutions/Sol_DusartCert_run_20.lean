-- Prove2me | solution 1 for DusartCert.run_20
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-10-16T20:45:44.649977+00:00
-- url     : https://prove2.me/submissions/5577d1d2-cd63-4b7f-aea8-2fbbdf61aa1d

import Definitions.Def_DusartCertData_20

theorem solution :
    DusartCert.run (2 ^ 64) 4823768287920834435 DusartCert.Gen.items20 (3050233, 44, 32996692933121375127, 295192142487132653, 3050233) =
    some (3206479, 46, 33058594441692615397, 295192152384528891, 3188987) := by
  decide +kernel
