-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f3_original_positive_band_lipschitz_source
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T14:46:34.605692+00:00
-- url     : https://prove2.me/submissions/f3481852-fa36-4316-a26e-54a9b850a109

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter
open scoped NNReal ENNReal
noncomputable section

/-- Compactly localised original UBV values are Lipschitz, yielding genuine small-jump L2 coefficients. -/
theorem solution
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (δ K : ℝ) (hδ : 0 < δ) (hδK : δ ≤ K)
    (hK : ENNReal.ofReal K < C) :
    ∃ B : ℝ, ∀ u ∈ Icc δ K, ∀ v ∈ Icc δ K,
      |w v - w u| ≤ B * |v - u| := by
  have hopen : IsOpen {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} := by
    change IsOpen (Ioi (0 : ℝ) ∩
      (fun y : ℝ => ENNReal.ofReal y) ⁻¹' Iio C)
    exact isOpen_Ioi.inter (isOpen_Iio.preimage ENNReal.continuous_ofReal)
  have hband : Icc δ K ⊆ {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} := by
    intro y hy
    exact ⟨lt_of_lt_of_le hδ hy.1,
      lt_of_le_of_lt (ENNReal.ofReal_le_ofReal hy.2) hK⟩
  have hderiv : ContinuousOn (deriv w)
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} :=
    hw_smooth.continuousOn_deriv_of_isOpen hopen (by norm_num)
  obtain ⟨B, hB⟩ :=
    isCompact_Icc.exists_bound_of_continuousOn (hderiv.mono hband)
  have hdiff : ∀ y ∈ Icc δ K, DifferentiableAt ℝ w y := by
    intro y hy
    exact (hw_smooth.differentiableOn (by norm_num)).differentiableAt
      (hopen.mem_nhds (hband hy))
  refine ⟨B, ?_⟩
  intro u hu v hv
  have hmean : ‖w v - w u‖ ≤ B * ‖v - u‖ :=
    Convex.norm_image_sub_le_of_norm_deriv_le hdiff hB
      (convex_Icc δ K) hu hv
  simpa only [Real.norm_eq_abs] using hmean
