-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb31_original_positive_discount_full_horizon_ENNReal_identity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T11:21:09.506215+00:00
-- url     : https://prove2.me/submissions/fe16b5d7-edf1-445d-af0d-48c344e8ff24

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bvb23_original_discounted_zero_contact_budget_identity
import Theorems.Thm_AvramDividend_Classical_avram_bvb28_original_discount_ENNReal_normalization_of_real_FTC
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    (q T : ℝ) (hq : 0 < q) (hT : 0 < T) :
    ENNReal.ofReal q *
      (∫⁻ t in Ioc (0 : ℝ) T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(volume : Measure ℝ)) +
      ENNReal.ofReal (Real.exp (-(q * T))) = 1  := by
  have hReal : q * (∫ t in Ioc (0 : ℝ) T,
      Real.exp (-(q * t)) ∂(volume : Measure ℝ)) +
      Real.exp (-(q * T)) = 1 := by
    have hBudget := avram_bvb23_original_discounted_zero_contact_budget_identity
      q T hq hT.le
    rw [intervalIntegral.integral_of_le hT.le] at hBudget
    simpa only [neg_mul] using hBudget
  exact avram_bvb28_original_discount_ENNReal_normalization_of_real_FTC
    q T hq hT hReal
