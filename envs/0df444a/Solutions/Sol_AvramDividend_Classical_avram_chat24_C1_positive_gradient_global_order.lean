-- Prove2me | solution 1 for AvramDividend.Classical.avram_chat24_C1_positive_gradient_global_order
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T07:51:34.125919+00:00
-- url     : https://prove2.me/submissions/4d1048a7-4683-4412-999f-2c3116e5f77d

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Positive gradient and continuity at zero imply global reserve monotonicity and nonnegativity. -/
theorem solution
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0) (hs : ContDiffOn ℝ 1 w (Ioi 0))
    (hg : ∀ y > 0, 1 ≤ deriv w y) :
    MonotoneOn w (Ici 0) ∧ ∀ y : ℝ, 0 ≤ w y := by
  have hdiff : DifferentiableOn ℝ w (Ioi (0 : ℝ)) :=
    hs.differentiableOn (by norm_num)
  have hmono : MonotoneOn w (Ici (0 : ℝ)) := by
    intro u hu v hv huv
    have hsub : Icc u v ⊆ Ici (0 : ℝ) := by
      intro y hy
      exact hu.trans hy.1
    have hcont : ContinuousOn w (Icc u v) :=
      hw_cont.mono hsub
    have hdiffI : DifferentiableOn ℝ w (interior (Icc u v)) := by
      rw [interior_Icc]
      apply hdiff.mono
      intro y hy
      exact lt_of_le_of_lt hu hy.1
    have hderiv : ∀ y ∈ interior (Icc u v), 0 ≤ deriv w y := by
      intro y hy
      have hypos : 0 < y := by
        rw [interior_Icc] at hy
        exact lt_of_le_of_lt hu hy.1
      linarith [hg y hypos]
    exact (monotoneOn_of_deriv_nonneg
      (convex_Icc u v) hcont hdiffI hderiv)
      ⟨le_refl u, huv⟩ ⟨huv, le_refl v⟩ huv
  refine ⟨hmono, ?_⟩
  intro y
  by_cases hy : 0 ≤ y
  · exact le_trans hw0 (hmono (by simp) hy hy)
  · have hz : y < 0 := lt_of_not_ge hy
    rw [hw_neg y hz]
