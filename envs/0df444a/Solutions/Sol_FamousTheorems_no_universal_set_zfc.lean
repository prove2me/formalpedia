-- Prove2me | solution 1 for FamousTheorems.no_universal_set_zfc
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T10:41:29.780954+00:00
-- url     : https://prove2.me/submissions/6edfd199-1ae5-4c77-90ce-9e01556bd318

import Mathlib

theorem solution : Class.univ ∉ Class.univ :=
  Class.univ_notMem_univ
