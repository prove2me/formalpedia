-- Prove2me | solution 1 for AvramDividend.Classical.chat04_esscher_finite_negative_laplace_lintegral_exact
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T21:50:44.824313+00:00
-- url     : https://prove2.me/submissions/732d1d66-bfd7-43e8-9ffa-aba6270bceee

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_finite_negative_exp_integrable
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_weighted_finite_horizon_negative_laplace
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (t : ℝ≥0) (θ ε : ℝ) (hθ : 0 ≤ θ)
    (hε : 0 ≤ ε) (hεθ : ε ≤ θ) :
    (∫⁻ ω, ENNReal.ofReal (Real.exp (-ε * X.X t ω)) ∂
      (P.withDensity (fun ω : Ω =>
        ENNReal.ofReal
          (Real.exp (θ * X.X t ω - (t : ℝ) * X.ψ θ))))) =
      ENNReal.ofReal
        (Real.exp ((t : ℝ) * (X.ψ (θ - ε) - X.ψ θ))) := by
  rw [← ofReal_integral_eq_lintegral_ofReal
    (chat04_esscher_finite_negative_exp_integrable X t θ ε hθ hε hεθ)
    (Filter.Eventually.of_forall (fun ω => Real.exp_nonneg _))]
  rw [chat04_esscher_weighted_finite_horizon_negative_laplace
    X t θ ε hθ hε hεθ]
