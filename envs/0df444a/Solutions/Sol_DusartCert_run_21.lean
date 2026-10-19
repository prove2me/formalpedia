-- Prove2me | solution 1 for DusartCert.run_21
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-10-16T20:45:46.103813+00:00
-- url     : https://prove2.me/submissions/89e3f5ae-1db1-49c3-b2ed-192f08917edc

import Definitions.Def_DusartCertData_21

theorem solution :
    DusartCert.run (2 ^ 64) 4823768287920834435 DusartCert.Gen.items21 (3206479, 46, 33058594441692615397, 295192152384528891, 3188987) =
    some (3352361, 29, 33113334439453082791, 295192160734121521, 3352361) := by
  decide +kernel
