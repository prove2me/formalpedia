-- Prove2me | solution 1 for AvramDividend.Classical.unbounded_esscher_tilt_global_monotone_of_corrected_exit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T18:06:56.085642+00:00
-- url     : https://prove2.me/submissions/d97405cf-ce5d-40de-a2df-868e5cd2f1f5

import Mathlib.Analysis.Complex.Exponential
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExitCorrected
import Theorems.Thm_AvramDividend_Classical_unbounded_scale_zero_origin_nonnegative_discount
import Theorems.Thm_AvramDividend_Classical_unbounded_esscher_tilted_scale_monotone_uniform_bound_of_corrected_exit
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The corrected exit comparison extends Esscher monotonicity across the zero boundary. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hnbv : ¬ X.BoundedVariation)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (hExit : ∀ a x : ℝ, 0 < a → 0 ≤ x → x ≤ a →
      twoSidedExitExpectationCorrected X q a x =
        ENNReal.ofReal (W x / W a)) :
    Monotone (fun x : ℝ => Real.exp (-(φ * x)) * W x) := by
  let V : ℝ → ℝ := fun x => Real.exp (-(φ * x)) * W x
  have hmono : MonotoneOn V (Ioi (0 : ℝ)) :=
    (unbounded_esscher_tilted_scale_monotone_uniform_bound_of_corrected_exit
      X q hq W hW hnbv φ hφ hroot V (by intro x hx; rfl) hExit).1
  have hWzero : W 0 = 0 :=
    unbounded_scale_zero_origin_nonnegative_discount
      X hnbv q (le_of_lt hq) W hW
  have hVnonneg : ∀ t : ℝ, 0 ≤ V t := by
    intro t
    change 0 ≤ Real.exp (-(φ * t)) * W t
    by_cases ht : t < 0
    · rw [hW.1 t ht]
      simp
    · exact mul_nonneg (le_of_lt (Real.exp_pos _))
        (hW.2.1 t (le_of_not_gt ht))
  change Monotone V
  intro s t hst
  by_cases hs : s ≤ 0
  · have hWsz : W s = 0 := by
      rcases lt_or_eq_of_le hs with hlt | heq
      · exact hW.1 s hlt
      · rw [heq]
        exact hWzero
    have hVsz : V s = 0 := by simp [V, hWsz]
    rw [hVsz]
    exact hVnonneg t
  · have hsp : 0 < s := lt_of_not_ge hs
    have htp : 0 < t := lt_of_lt_of_le hsp hst
    exact hmono hsp htp hst
