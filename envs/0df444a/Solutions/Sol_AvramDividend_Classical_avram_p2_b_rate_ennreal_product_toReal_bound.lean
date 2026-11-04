-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_b_rate_ennreal_product_toReal_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T21:36:08.627835+00:00
-- url     : https://prove2.me/submissions/944daaaf-7e65-471f-adba-70a2bf723dc8

import Mathlib.Data.ENNReal.Real

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped ENNReal

theorem solution
    (a C : ℝ) (b : ENNReal) (ha : 0 ≤ a) (hC : 0 ≤ C)
    (hab : ENNReal.ofReal a * b ≤ ENNReal.ofReal C) :
    a * b.toReal ≤ C := by
  have htop : ENNReal.ofReal C ≠ ⊤ := by simp
  have hb := ENNReal.toReal_mono htop hab
  simpa [ENNReal.toReal_mul, ENNReal.toReal_ofReal ha,
    ENNReal.toReal_ofReal hC] using hb
