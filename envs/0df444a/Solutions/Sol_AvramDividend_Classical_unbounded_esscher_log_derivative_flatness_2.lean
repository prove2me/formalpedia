-- Prove2me | solution 2 for AvramDividend.Classical.unbounded_esscher_log_derivative_flatness
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T14:04:03.717014+00:00
-- url     : https://prove2.me/submissions/03db2c71-357e-45c7-b30c-d94cc392a610

import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_esscher_tilted_uniform_bound_of_monotone
import Theorems.Thm_AvramDividend_Classical_positive_monotoneOn_bounded_tendsto_positive
import Theorems.Thm_AvramDividend_Classical_tendsto_deriv_zero_of_concave_finite_limit

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter
open scoped NNReal ENNReal Topology

/-!
The given Esscher monotonicity already implies a finite upper bound via the
scale-function Laplace transform. The limiting derivative of log V follows
from finite monotone convergence and its assumed antitonicity. This avoids
importing the open unbounded Esscher limit theorem.
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
  have hupper : ∃ C : ℝ, ∀ x : ℝ, 0 < x → V x ≤ C := by
    refine ⟨Real.exp 2 * (φ / q), ?_⟩
    intro x hx
    exact esscher_tilted_uniform_bound_of_monotone
      X q hq W hW φ hφ hroot V hV htilt x hx
  obtain ⟨L, hL, hVlim⟩ :=
    positive_monotoneOn_bounded_tendsto_positive V hVpos htilt hupper
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
