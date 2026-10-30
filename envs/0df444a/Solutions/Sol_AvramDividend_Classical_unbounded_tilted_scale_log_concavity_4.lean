-- Prove2me | solution 4 for AvramDividend.Classical.unbounded_tilted_scale_log_concavity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T18:49:49.207363+00:00
-- url     : https://prove2.me/submissions/36f092ab-8c3a-4915-82d1-875503adb848

import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.FDeriv.Congr
import Mathlib.Analysis.Convex.Function
import Mathlib.Tactic.FunProp
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExitCorrected
import Theorems.Thm_AvramDividend_Classical_unbounded_corrected_exit_scale_identity
import Theorems.Thm_AvramDividend_Classical_unbounded_tilted_scale_log_concavity_of_corrected_exit

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

/-- Local untwisting transfers differentiability of V to W. The corrected
exit identity and the proved cross-derivative criterion give log-concavity. -/
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
    rw [hV t ht]
    rw [← mul_assoc, ← Real.exp_add]
    simp
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
