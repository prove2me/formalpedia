-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f3_source_interior_compact_derivative_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T14:31:41.712818+00:00
-- url     : https://prove2.me/submissions/b5605815-cdff-4ce4-a264-ffdc9663fe0a

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Source interior C2 smoothness bounds the original derivative on compact stopped-state bands. -/
theorem solution
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hopen : IsOpen {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (a b : ℝ)
    (hband : Icc a b ⊆ {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) :
    ∃ B : ℝ, ∀ y ∈ Icc a b, |deriv w y| ≤ B := by
  have hderiv : ContinuousOn (deriv w)
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} :=
    hw_smooth.continuousOn_deriv_of_isOpen hopen (by norm_num)
  have hlocal : ContinuousOn (deriv w) (Icc a b) := hderiv.mono hband
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hlocal
  refine ⟨B, ?_⟩
  intro y hy
  simpa only [Real.norm_eq_abs] using hB y hy
