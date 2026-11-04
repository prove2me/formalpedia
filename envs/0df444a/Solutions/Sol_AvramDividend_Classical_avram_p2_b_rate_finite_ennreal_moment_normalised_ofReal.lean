-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_b_rate_finite_ennreal_moment_normalised_ofReal
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T22:17:39.187203+00:00
-- url     : https://prove2.me/submissions/a212b6f2-cc37-4426-bcc8-b48149439197

import Mathlib.Data.ENNReal.Inv
import Mathlib.Data.ENNReal.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped ENNReal

theorem solution (a : ℝ≥0∞) (ha : a ≠ ⊤) (h : ℝ) (hh : 0 < h) :
  ENNReal.ofReal (a.toReal / h) = a / ENNReal.ofReal h := by
  rw [ENNReal.ofReal_div_of_pos hh, ENNReal.ofReal_toReal ha]
