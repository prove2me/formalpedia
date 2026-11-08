-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_strict12_finite_cap_value_uniform_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T09:32:35.558553+00:00
-- url     : https://prove2.me/submissions/a52661b1-7214-4c0e-a7f6-84cf6698dfda

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- A finite surplus cap makes the continuous candidate bounded along every
    nonnegative admissible surplus, including both cap boundaries. -/
theorem solution
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hFinite : C ≠ ⊤)
    (hw_cont : ContinuousOn w (Ici 0)) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ y : ℝ, 0 ≤ y → ENNReal.ofReal y ≤ C → |w y| ≤ K := by
  have hCont : ContinuousOn w (Icc (0 : ℝ) C.toReal) :=
    hw_cont.mono (by
      intro y hy
      exact hy.1)
  obtain ⟨K, hK⟩ := isCompact_Icc.exists_bound_of_continuousOn hCont
  refine ⟨max K 0, le_max_right _ _, ?_⟩
  intro y hy0 hyC
  have hy : y ≤ C.toReal :=
    (ENNReal.ofReal_le_iff_le_toReal hFinite).mp hyC
  have hW := hK y ⟨hy0, hy⟩
  simpa only [Real.norm_eq_abs] using
    (hW.trans (le_max_left K 0))
