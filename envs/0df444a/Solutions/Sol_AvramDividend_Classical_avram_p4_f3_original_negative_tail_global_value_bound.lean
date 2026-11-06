-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f3_original_negative_tail_global_value_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T14:42:38.307956+00:00
-- url     : https://prove2.me/submissions/2ce168da-3661-4b30-b2d1-225844e78a37

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Original UBV verification value is bounded over the whole negative jump tail below finite K. -/
theorem solution
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (K : ℝ) (hK : 0 ≤ K) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ y : ℝ, y ≤ K → |w y| ≤ A := by
  have hsub : Icc (0 : ℝ) K ⊆ Ici (0 : ℝ) := by
    intro y hy
    exact hy.1
  obtain ⟨A, hA⟩ :=
    isCompact_Icc.exists_bound_of_continuousOn (hw_cont.mono hsub)
  have hA0 : 0 ≤ A := by
    exact le_trans (norm_nonneg (w 0)) (hA 0 ⟨le_refl _, hK⟩)
  refine ⟨A, hA0, ?_⟩
  intro y hyK
  by_cases hy0 : y < 0
  · rw [hw_neg y hy0, abs_zero]
    exact hA0
  · have hy0' : 0 ≤ y := le_of_not_gt hy0
    simpa only [Real.norm_eq_abs] using hA y ⟨hy0', hyK⟩
