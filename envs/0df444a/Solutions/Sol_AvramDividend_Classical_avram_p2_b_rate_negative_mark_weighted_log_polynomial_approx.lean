-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_b_rate_negative_mark_weighted_log_polynomial_approx
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T17:03:25.081236+00:00
-- url     : https://prove2.me/submissions/9d6d54e6-df64-423e-a520-ba30a1851bf8

import Mathlib
import Mathlib.Topology.ContinuousMap.Weierstrass
import Theorems.Thm_AvramDividend_Classical_avram_p2_b_rate_weighted_log_test_continuous_all_real

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Topology

theorem solution
    (f : ℝ → ℝ) (hf : Continuous f) (a ε : ℝ) (hε : 0 < ε)
    (hflower : ∀ y : ℝ, y < a → f y = 0)
    (hfupper : ∀ y : ℝ, -ε < y → f y = 0)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ p : Polynomial ℝ, ∀ z ∈ Set.Icc (0 : ℝ) 1,
      |p.eval z - f (Real.log z) / (z - 1) ^ 4| < δ := by
  have hg : Continuous (fun z : ℝ =>
      f (Real.log z) / (z - 1) ^ 4) :=
    AvramDividend.Classical.avram_p2_b_rate_weighted_log_test_continuous_all_real
      f hf a ε hε hflower hfupper
  exact exists_polynomial_near_of_continuousOn
    0 1 (fun z : ℝ => f (Real.log z) / (z - 1) ^ 4)
    hg.continuousOn δ hδ
