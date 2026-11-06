-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f3_original_positive_band_derivative_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T14:46:27.35851+00:00
-- url     : https://prove2.me/submissions/fa73fe5f-63d7-42a5-ae79-e5756243134e

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter
open scoped NNReal ENNReal
noncomputable section

/-- On every positive compact reserve band strictly below the cap, the source derivative is bounded. -/
theorem solution
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (δ K : ℝ) (hδ : 0 < δ) (hδK : δ ≤ K)
    (hK : ENNReal.ofReal K < C) :
    ∃ B : ℝ, ∀ y ∈ Icc δ K, |deriv w y| ≤ B := by
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
  have hlocal : ContinuousOn (deriv w) (Icc δ K) := hderiv.mono hband
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hlocal
  refine ⟨B, ?_⟩
  intro y hy
  simpa only [Real.norm_eq_abs] using hB y hy
