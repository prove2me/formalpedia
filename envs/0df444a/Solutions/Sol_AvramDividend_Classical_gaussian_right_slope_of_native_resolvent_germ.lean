-- Prove2me | solution 1 for AvramDividend.Classical.gaussian_right_slope_of_native_resolvent_germ
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T11:04:20.22716+00:00
-- url     : https://prove2.me/submissions/e12dcb2a-78f1-4cb3-9b4d-a5f924247605

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic.FieldSimp
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_causal_volterra_origin_value_of_vanishing_residual
import Theorems.Thm_AvramDividend_Classical_esscher_untilt_deriv_right_limit_of_resolvent
open AvramDividend.Classical MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hσ : 0 < X.σ)
    (W V g C : ℝ → ℝ) (φ : ℝ)
    (hW : ∀ x : ℝ, 0 < x → W x = Real.exp (φ * x) * V x)
    (hVlim : Tendsto V (𝓝[>] (0 : ℝ)) (𝓝 0))
    (hg : ContinuousOn g (Ici (0 : ℝ)))
    (hC : Tendsto C (𝓝[>] (0 : ℝ)) (𝓝 0))
    (heq : ∀ x : ℝ, 0 < x → (X.σ ^ 2 / 2) * g x + C x = 1)
    (hVderiv : ∀ x : ℝ, 0 < x → HasDerivAt V (g x) x) :
    Tendsto (deriv W) (𝓝[>] (0 : ℝ)) (𝓝 (2 / X.σ ^ 2)) := by
  have h0 := AvramDividend.Classical.causal_volterra_origin_value_of_vanishing_residual (X.σ ^ 2 / 2)
    g C (by positivity) hg hC heq
  have h1 : g 0 = 2 / X.σ ^ 2 := by rw [h0]; field_simp
  exact AvramDividend.Classical.esscher_untilt_deriv_right_limit_of_resolvent W V g φ _ hW hVlim hg h1
    hVderiv
