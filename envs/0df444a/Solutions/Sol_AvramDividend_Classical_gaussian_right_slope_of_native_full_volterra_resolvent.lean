-- Prove2me | solution 1 for AvramDividend.Classical.gaussian_right_slope_of_native_full_volterra_resolvent
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T12:48:14.058328+00:00
-- url     : https://prove2.me/submissions/e4311c20-1223-4e0a-a442-942977af199b

import Mathlib.Analysis.Complex.Exponential
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_causal_continuousOn_nonnegative_locally_bounded
import Theorems.Thm_AvramDividend_Classical_causal_full_l1_kernel_vanishes_at_origin
import Theorems.Thm_AvramDividend_Classical_gaussian_right_slope_of_native_resolvent_germ
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter
open scoped Topology NNReal ENNReal

/-- The native Gaussian Volterra resolvent gives the exact scale right slope. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hσ : 0 < X.σ)
    (W V g K : ℝ → ℝ) (φ β : ℝ)
    (hW : ∀ x : ℝ, 0 < x → W x = Real.exp (φ * x) * V x)
    (hVlim : Tendsto V (𝓝[>] (0 : ℝ)) (𝓝 0))
    (hK : IntegrableOn K (Ioi (0 : ℝ)) volume)
    (hg : ContinuousOn g (Ici (0 : ℝ)))
    (hgeq : ∀ x : ℝ, 0 < x →
      (X.σ ^ 2 / 2) * g x +
        (∫ s in Ioc (0 : ℝ) x,
          (β + K (x - s)) * g s ∂volume) = 1)
    (hVderiv : ∀ x : ℝ, 0 < x → HasDerivAt V (g x) x) :
    Tendsto (deriv W) (𝓝[>] (0 : ℝ)) (𝓝 (2 / X.σ ^ 2)) := by
  have hgb : ∀ R : ℝ, 0 < R →
      ∃ C : ℝ, ∀ s : ℝ, s ∈ Ioc (0 : ℝ) R → |g s| ≤ C :=
    causal_continuousOn_nonnegative_locally_bounded g hg
  have hC0 : Tendsto (fun x : ℝ =>
      ∫ s in Ioc (0 : ℝ) x, (β + K (x - s)) * g s ∂volume)
      (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    causal_full_l1_kernel_vanishes_at_origin K g β hK hg hgb
  exact gaussian_right_slope_of_native_resolvent_germ X hσ
    W V g (fun x : ℝ =>
      ∫ s in Ioc (0 : ℝ) x, (β + K (x - s)) * g s ∂volume)
    φ hW hVlim hg hC0 hgeq hVderiv
