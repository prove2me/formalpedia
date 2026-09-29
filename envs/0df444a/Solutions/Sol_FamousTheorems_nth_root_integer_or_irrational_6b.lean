-- Prove2me | solution 1 for FamousTheorems.nth_root_integer_or_irrational_6b
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T11:26:08.974051+00:00
-- url     : https://prove2.me/submissions/9cb96509-8b5d-469d-8eeb-3fc18dc71afa

import Mathlib

theorem solution {x : ℝ} (n : ℕ) (m : ℤ) (hxr : x ^ n = m) (hv : ¬∃ y : ℤ, x = y) (hnpos : 0 < n) : Irrational x :=
  irrational_nrt_of_notint_nrt n m hxr hv hnpos
