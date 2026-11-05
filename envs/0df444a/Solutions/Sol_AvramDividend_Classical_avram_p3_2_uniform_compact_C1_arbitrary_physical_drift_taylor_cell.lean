-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_2_uniform_compact_C1_arbitrary_physical_drift_taylor_cell
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T00:36:00.632392+00:00
-- url     : https://prove2.me/submissions/bf1b3e58-3ff3-42e5-99b9-6b90e6838fb3

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_d_bvmesh_local_C1_taylor_from_derivative_oscillation

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- Physical pure drift Taylor remainder on a compact original subcap band. -/
theorem solution
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hwC1 : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hOpen : IsOpen {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (a b : ℝ)
    (hBand : Set.Icc a b ⊆
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) :
    ∀ ε : ℝ, 0 < ε →
      ∃ δ : ℝ, 0 < δ ∧ ∀ z c : ℝ,
        Set.uIcc z (z + c) ⊆ Set.Icc a b →
        |c| < δ →
        |w (z + c) - w z - deriv w z * c| ≤ ε * |c| := by
  have hCont : ContinuousOn (deriv w)
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} :=
    hwC1.continuousOn_deriv_of_isOpen hOpen (by norm_num)
  have hUnif : UniformContinuousOn (deriv w) (Set.Icc a b) :=
    isCompact_Icc.uniformContinuousOn_of_continuous (hCont.mono hBand)
  intro ε hε
  obtain ⟨δ, hδ, hControl⟩ :=
    (Metric.uniformContinuousOn_iff.mp hUnif) ε hε
  refine ⟨δ, hδ, ?_⟩
  intro z c hInside hSmall
  have hCell : Set.uIcc z (z + c) ⊆
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} :=
    hInside.trans hBand
  have hInt : IntervalIntegrable (deriv w) volume z (z + c) :=
    (hCont.mono hCell).intervalIntegrable
  have hOsc : ∀ v ∈ Set.uIoc z (z + c),
      |deriv w v - deriv w z| ≤ ε := by
    intro v hv
    have hvIcc : v ∈ Set.uIcc z (z + c) :=
      Set.uIoc_subset_uIcc hv
    have hzBand : z ∈ Set.Icc a b :=
      hInside Set.left_mem_uIcc
    have hdist : dist v z < δ := by
      rw [Real.dist_eq]
      calc
        |v - z| ≤ |(z + c) - z| :=
          Set.abs_sub_left_of_mem_uIcc hvIcc
        _ = |c| := by simp only [add_sub_cancel_left]
        _ < δ := hSmall
    exact le_of_lt (by
      simpa only [Real.dist_eq] using
        hControl v (hInside hvIcc) z hzBand hdist)
  have hDiff : ∀ v ∈ Set.uIcc z (z + c),
      DifferentiableAt ℝ w v := by
    intro v hv
    have hvInside := hCell hv
    have hWithin : DifferentiableWithinAt ℝ w
        {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} v :=
      (hwC1.differentiableOn (by norm_num)) v hvInside
    exact hWithin.differentiableAt (hOpen.mem_nhds hvInside)
  have hTaylor :=
    avram_p3_d_bvmesh_local_C1_taylor_from_derivative_oscillation
      w z (z + c) ε hDiff hInt hOsc
  simpa only [add_sub_cancel_left] using hTaylor
