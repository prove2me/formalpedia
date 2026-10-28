-- Prove2me | solution 3 for AvramDividend.Classical.unbounded_tilted_scale_log_concavity
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T10:05:28.316608+00:00
-- url     : https://prove2.me/submissions/0626efb5-c0c2-4860-b06f-ec17cd8aab88
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Basic
import Definitions.Def_AvramDividend_Classical_TwoSidedExitCorrected
import Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_unbounded_variation
import Theorems.Thm_AvramDividend_Classical_unbounded_corrected_exit_scale_identity
import Theorems.Thm_AvramDividend_Classical_unbounded_tilted_scale_cross_derivative_of_corrected_exit
import Theorems.Thm_AvramDividend_Classical_positive_cross_derivative_log_concavity

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter
open scoped NNReal ENNReal Topology

/-- A corrected exit identity yields tilted log-concavity through
the cross-derivative inequality and local exponential untwisting. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hnbv : ¬ X.BoundedVariation)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (V : ℝ → ℝ)
    (hV : ∀ x : ℝ, 0 < x → V x = Real.exp (-(φ * x)) * W x)
    (hVdiff : ∀ x : ℝ, 0 < x → HasDerivAt V (deriv V x) x) :
    ConcaveOn ℝ (Ioi (0 : ℝ)) (fun x : ℝ => Real.log (V x)) := by
  let f : ℝ → ℝ := fun z => Real.exp (-φ * z) * W z
  have hpos : ∀ z : ℝ, 0 < z → 0 < W z :=
    scaleFunction_strict_pos_of_unbounded_variation X q W hW hnbv
  have hVpos : ∀ z : ℝ, 0 < z → 0 < V z := by
    intro z hz
    rw [hV z hz]
    exact mul_pos (Real.exp_pos _) (hpos z hz)
  have hExit : ∀ a z : ℝ, 0 < a → 0 < z → z ≤ a →
      twoSidedExitExpectationCorrected X q a z =
        ENNReal.ofReal (W z / W a) := by
    intro a z ha hz hza
    exact unbounded_corrected_exit_scale_identity
      X q hq W hW hnbv a z ha (le_of_lt hz) hza
  have hVlocal (z : ℝ) (hz : 0 < z) : V =ᶠ[𝓝 z] f := by
    filter_upwards [isOpen_Ioi.mem_nhds hz] with t ht
    simpa only [f, neg_mul] using hV t ht
  have hWlocal (z : ℝ) (hz : 0 < z) :
      W =ᶠ[𝓝 z] (fun t : ℝ => Real.exp (φ * t) * V t) := by
    filter_upwards [isOpen_Ioi.mem_nhds hz] with t ht
    rw [hV t ht]
    simp only [← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul]
  have hWdiff (z : ℝ) (hz : 0 < z) : DifferentiableAt ℝ W z := by
    have he : DifferentiableAt ℝ (fun t : ℝ => Real.exp (φ * t)) z :=
      (Real.differentiableAt_exp).comp z
        (differentiableAt_id.const_mul φ)
    have hp : DifferentiableAt ℝ
        (fun t : ℝ => Real.exp (φ * t) * V t) z :=
      he.mul ((hVdiff z hz).differentiableAt)
    exact hp.congr_of_eventuallyEq (hWlocal z hz)
  have hcross : ∀ x y : ℝ, 0 < x → x ≤ y →
      deriv V y * V x ≤ deriv V x * V y := by
    intro x y hx hxy
    have hy : 0 < y := lt_of_lt_of_le hx hxy
    have hdx : deriv f x = deriv V x :=
      ((hVdiff x hx).congr_of_eventuallyEq (hVlocal x hx).symm).deriv
    have hdy : deriv f y = deriv V y :=
      ((hVdiff y hy).congr_of_eventuallyEq (hVlocal y hy).symm).deriv
    have hc := unbounded_tilted_scale_cross_derivative_of_corrected_exit
      X q hq W hW hnbv hExit φ x y hx hxy
      (hWdiff x hx) (hWdiff y hy)
    change deriv f y * f x ≤ deriv f x * f y at hc
    have hfx : f x = V x := by
      simpa only [f, neg_mul] using (hV x hx).symm
    have hfy : f y = V y := by
      simpa only [f, neg_mul] using (hV y hy).symm
    rw [hdx, hdy, hfx, hfy] at hc
    exact hc
  exact positive_cross_derivative_log_concavity V hVpos hVdiff hcross
