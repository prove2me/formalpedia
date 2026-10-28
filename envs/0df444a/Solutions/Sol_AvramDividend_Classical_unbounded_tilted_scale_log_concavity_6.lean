-- Prove2me | solution 6 for AvramDividend.Classical.unbounded_tilted_scale_log_concavity
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T11:17:35.192868+00:00
-- url     : https://prove2.me/submissions/0ee61700-92f9-4745-baf1-a924e0c51f98
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExitCorrected
import Theorems.Thm_AvramDividend_Classical_unbounded_corrected_exit_scale_identity
import Theorems.Thm_AvramDividend_Classical_unbounded_tilted_scale_log_concavity_of_corrected_exit
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter
open scoped NNReal ENNReal Topology

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
  have hWexpr (t : ℝ) (ht : 0 < t) :
      W t = Real.exp (φ * t) * V t := by
    conv_rhs => rw [hV t ht]
    rw [← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul]
  have hWdiff : ∀ x : ℝ, 0 < x → DifferentiableAt ℝ W x := by
    intro x hx
    have hlocal :
        W =ᶠ[nhds x] (fun t : ℝ => Real.exp (φ * t) * V t) := by
      filter_upwards [eventually_gt_nhds hx] with t ht
      exact hWexpr t ht
    have hlinear : DifferentiableAt ℝ (fun t : ℝ => φ * t) x := by
      fun_prop
    have hproduct :
        DifferentiableAt ℝ (fun t : ℝ => Real.exp (φ * t) * V t) x :=
      hlinear.exp.mul ((hVdiff x hx).differentiableAt)
    exact hproduct.congr_of_eventuallyEq hlocal
  have hconc :
      ConcaveOn ℝ (Ioi (0 : ℝ))
        (fun z : ℝ => Real.log (Real.exp (-φ * z) * W z)) :=
    AvramDividend.Classical.unbounded_tilted_scale_log_concavity_of_corrected_exit
      X q hq W hW hnbv
      (fun a x ha hx hxa =>
        AvramDividend.Classical.unbounded_corrected_exit_scale_identity
          X q hq W hW hnbv a x ha (le_of_lt hx) hxa)
      φ hWdiff
  apply hconc.congr
  intro z hz
  simpa only [hV z hz, neg_mul]
