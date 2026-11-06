-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f3_original_negative_mark_two_state_squared_difference_dominated
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T17:11:33.04146+00:00
-- url     : https://prove2.me/submissions/42672fad-2c31-48a2-b4a4-dad44ccca283

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_negative_mark_kernel_uniform_quadratic_min_bound
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Two original stopped-state jump coefficients share one Levy-dominated squared-difference bound. -/
theorem solution
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (δ K : ℝ) (hδ : 0 < δ) (hδK : δ ≤ K)
    (hK : ENNReal.ofReal K < C) :
    ∃ Q : ℝ, 0 ≤ Q ∧
      ∀ u ∈ Icc δ K, ∀ v ∈ Icc δ K, ∀ z : ℝ, z < 0 →
        ((w (u + z) - w u) - (w (v + z) - w v)) ^ 2 ≤
          Q * min 1 (z ^ 2) := by
  obtain ⟨M, hM0, hM⟩ :=
    avram_p4_f3_original_negative_mark_kernel_uniform_quadratic_min_bound
      w C hw_cont hw_neg hw_smooth δ K hδ hδK hK
  refine ⟨4 * M, mul_nonneg (by norm_num) hM0, ?_⟩
  intro u hu v hv z hz
  have huSq := hM u hu z hz
  have hvSq := hM v hv z hz
  have hSumSq :
      0 ≤ ((w (u + z) - w u) + (w (v + z) - w v)) ^ 2 :=
    sq_nonneg _
  nlinarith
