-- Prove2me | solution 1 for FamousTheorems.complex_exists_root
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-21T21:52:37.313606+00:00
-- url     : https://prove2.me/submissions/b450d7fc-f92f-48d1-926b-1fdc25cd4563

import Mathlib

theorem solution : ∀ {f : Polynomial ℂ}, 0 < f.degree → ∃ z, f.IsRoot z :=
  Complex.exists_root
