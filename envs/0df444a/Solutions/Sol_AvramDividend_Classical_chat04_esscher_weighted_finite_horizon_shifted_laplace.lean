-- Prove2me | solution 1 for AvramDividend.Classical.chat04_esscher_weighted_finite_horizon_shifted_laplace
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T21:14:13.531079+00:00
-- url     : https://prove2.me/submissions/635da355-419f-423e-ae06-7eece5991021

import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Probability.Process.Adapted
import Mathlib.Analysis.Complex.Exponential
import Theorems.Thm_AvramDividend_Classical_esscher_finite_horizon_shifted_exponential_moment
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
    (t : ℝ≥0) (θ η : ℝ) (hθ : 0 ≤ θ) (hη : 0 ≤ η) :
    (∫ ω, Real.exp (η * X.X t ω) ∂
      (P.withDensity (fun ω : Ω =>
        ENNReal.ofReal (Real.exp (θ * X.X t ω - (t : ℝ) * X.ψ θ))))) =
      Real.exp ((t : ℝ) * (X.ψ (θ + η) - X.ψ θ)) := by
  have hmX : Measurable (X.X t) := X.adapted.measurable
  have hmReal : Measurable (fun ω : Ω =>
      Real.exp (θ * X.X t ω - (t : ℝ) * X.ψ θ)) :=
    Real.continuous_exp.measurable.comp
      ((measurable_const.mul hmX).sub measurable_const)
  have hmF : Measurable (fun ω : Ω =>
      ENNReal.ofReal (Real.exp (θ * X.X t ω - (t : ℝ) * X.ψ θ))) :=
    ENNReal.measurable_ofReal.comp hmReal
  have hfin : ∀ᵐ ω ∂P,
      ENNReal.ofReal (Real.exp (θ * X.X t ω - (t : ℝ) * X.ψ θ)) < ∞ :=
    Filter.Eventually.of_forall (fun ω => ENNReal.ofReal_lt_top)
  calc
    (∫ ω, Real.exp (η * X.X t ω) ∂
      (P.withDensity (fun ω : Ω =>
        ENNReal.ofReal (Real.exp (θ * X.X t ω - (t : ℝ) * X.ψ θ))))) =
      ∫ ω, (ENNReal.ofReal (Real.exp (θ * X.X t ω - (t : ℝ) * X.ψ θ))).toReal •
        Real.exp (η * X.X t ω) ∂P := by
        exact integral_withDensity_eq_integral_toReal_smul hmF hfin _
    _ = ∫ ω, Real.exp (θ * X.X t ω - (t : ℝ) * X.ψ θ) *
        Real.exp (η * X.X t ω) ∂P := by
        apply integral_congr_ae
        filter_upwards [] with ω
        simp only [ENNReal.toReal_ofReal (Real.exp_nonneg _), smul_eq_mul]
    _ = _ := esscher_finite_horizon_shifted_exponential_moment X t θ η hθ hη
