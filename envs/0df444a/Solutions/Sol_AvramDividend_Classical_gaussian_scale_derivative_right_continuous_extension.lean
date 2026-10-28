-- Prove2me | solution 1 for AvramDividend.Classical.gaussian_scale_derivative_right_continuous_extension
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T13:22:45.473347+00:00
-- url     : https://prove2.me/submissions/70a2af4e-fe2a-4445-9b08-52e548a98a19

import Mathlib.Topology.NhdsWithin
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleDeriv_continuous_of_gaussian
import Theorems.Thm_AvramDividend_Classical_scaleFunction_derivRightLimit_at_zero_eq_two_over_sigma
import Theorems.Thm_AvramDividend_Classical_causal_continuousOn_Ici_of_positive_limit
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter
open scoped Topology NNReal ENNReal

/-- Extend W' continuously from positive reserves by the Gaussian right slope. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hσ : 0 < X.σ) (hzero : W 0 = 0)
    (hderiv : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt W (deriv W x) x) :
    ContinuousOn (fun x : ℝ => if x = 0 then 2 / X.σ ^ 2 else deriv W x)
      (Ici (0 : ℝ)) := by
  let f : ℝ → ℝ := fun x => if x = 0 then 2 / X.σ ^ 2 else deriv W x
  have hpos : ∀ x : ℝ, 0 < x → f x = deriv W x := by
    intro x hx
    simp [f, ne_of_gt hx]
  have hfpos : ContinuousOn f (Ioi (0 : ℝ)) := by
    apply (scaleDeriv_continuous_of_gaussian X hσ q hq W hW).congr
    intro x hx
    exact hpos x hx
  have hscale : Tendsto (deriv W) (𝓝[>] (0 : ℝ))
      (𝓝 (2 / X.σ ^ 2)) :=
    scaleFunction_derivRightLimit_at_zero_eq_two_over_sigma
      X q hq W hW hσ hzero hderiv
  have heq : (deriv W) =ᶠ[𝓝[>] (0 : ℝ)] f := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact (hpos x hx).symm
  have hflt : Tendsto f (𝓝[>] (0 : ℝ))
      (𝓝 (2 / X.σ ^ 2)) := hscale.congr' heq
  have hlim : Tendsto f (𝓝[>] (0 : ℝ)) (𝓝 (f 0)) := by
    simpa [f] using hflt
  exact causal_continuousOn_Ici_of_positive_limit f hfpos hlim
