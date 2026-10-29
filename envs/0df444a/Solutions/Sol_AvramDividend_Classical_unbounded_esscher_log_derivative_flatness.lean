-- Prove2me | solution 1 for AvramDividend.Classical.unbounded_esscher_log_derivative_flatness
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T22:22:10.38007+00:00
-- url     : https://prove2.me/submissions/b331fb33-4371-4dad-8d33-9a41eff14088

import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_unbounded_esscher_tilted_scale_positive_finite_limit
import Theorems.Thm_AvramDividend_Classical_tendsto_deriv_zero_of_concave_finite_limit
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter
open scoped NNReal ENNReal Topology

/-!
The derivative of the logarithm of the Esscher tilt becomes flat.
The only stochastic input is the positive finite tilted-scale limit.
-/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hnbv : ¬ X.BoundedVariation)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (V : ℝ → ℝ)
    (hV : ∀ x : ℝ, 0 < x →
      V x = Real.exp (-(φ * x)) * W x)
    (hVpos : ∀ x : ℝ, 0 < x → 0 < V x)
    (hVdiff : ∀ x : ℝ, 0 < x → DifferentiableAt ℝ V x)
    (htilt : MonotoneOn V (Ioi (0 : ℝ)))
    (hanti : AntitoneOn
      (fun x : ℝ => deriv (fun y : ℝ => Real.log (V y)) x)
      (Ioi (0 : ℝ))) :
    Tendsto
      (fun x : ℝ => deriv (fun y : ℝ => Real.log (V y)) x)
      atTop (nhds (0 : ℝ)) := by
  obtain ⟨L, hL, hVlim⟩ :=
    unbounded_esscher_tilted_scale_positive_finite_limit
      X q hq W hW hnbv φ hφ hroot V hV
  let f : ℝ → ℝ := fun x => Real.log (V x)
  have hfcont : ContinuousOn f (Ioi (0 : ℝ)) := by
    intro x hx
    exact ((Real.continuousAt_log (hVpos x hx).ne').comp
      (hVdiff x hx).continuousAt).continuousWithinAt
  have hfdiff : ∀ x : ℝ, 0 < x → DifferentiableAt ℝ f x := by
    intro x hx
    exact (Real.differentiableAt_log (hVpos x hx).ne').comp x (hVdiff x hx)
  have hfdiffOn : DifferentiableOn ℝ f (interior (Ioi (0 : ℝ))) := by
    simpa only [interior_Ioi] using
      (show DifferentiableOn ℝ f (Ioi (0 : ℝ)) from
        fun x hx => (hfdiff x hx).differentiableWithinAt)
  have hfanti : AntitoneOn (deriv f) (interior (Ioi (0 : ℝ))) := by
    simpa only [interior_Ioi, f] using hanti
  have hfconc : ConcaveOn ℝ (Ioi (0 : ℝ)) f :=
    hfanti.concaveOn_of_deriv (convex_Ioi _) hfcont hfdiffOn
  have hflim : Tendsto f atTop (nhds (Real.log L)) :=
    (Real.continuousAt_log hL.ne').tendsto.comp hVlim
  simpa only [f] using
    tendsto_deriv_zero_of_concave_finite_limit f (Real.log L)
      hfconc hfdiff hflim
