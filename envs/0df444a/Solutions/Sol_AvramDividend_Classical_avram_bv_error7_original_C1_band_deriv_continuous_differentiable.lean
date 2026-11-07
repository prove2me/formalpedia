-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_error7_original_C1_band_deriv_continuous_differentiable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T09:52:36.027829+00:00
-- url     : https://prove2.me/submissions/76d81471-4d1f-4d91-90e8-c6e5923bf071

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.SetSemiring
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- The genuine C1 value function is differentiable and has a
continuous derivative on every compact strictly interior cap band. -/
theorem solution
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hwC1 : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hOpen : IsOpen {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (a b : ℝ)
    (hBand : Set.Icc a b ⊆
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) :
    ContinuousOn (deriv w) (Set.Icc a b) ∧
      (∀ y ∈ Set.Icc a b, DifferentiableAt ℝ w y) := by
  have hDiffOn : DifferentiableOn ℝ w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} :=
    hwC1.differentiableOn_one
  have hDerContOpen : ContinuousOn (deriv w)
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} :=
    hwC1.continuousOn_deriv_of_isOpen hOpen le_rfl
  refine ⟨hDerContOpen.mono hBand, ?_⟩
  intro y hy
  have hmem := hBand hy
  exact (hDiffOn y hmem).differentiableAt (hOpen.mem_nhds hmem)
