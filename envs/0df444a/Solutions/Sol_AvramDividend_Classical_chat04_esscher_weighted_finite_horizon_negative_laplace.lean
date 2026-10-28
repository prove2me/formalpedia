-- Prove2me | solution 1 for AvramDividend.Classical.chat04_esscher_weighted_finite_horizon_negative_laplace
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T21:32:44.818323+00:00
-- url     : https://prove2.me/submissions/b2084e11-4f05-4a91-ab18-d0e666096d1c

import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Probability.Process.Adapted
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic.Ring
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
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
    (t : ℝ≥0) (θ ε : ℝ)
    (hθ : 0 ≤ θ) (hε : 0 ≤ ε) (hεθ : ε ≤ θ) :
    (∫ ω, Real.exp (-ε * X.X t ω) ∂
      (P.withDensity (fun ω : Ω =>
        ENNReal.ofReal (Real.exp (θ * X.X t ω - (t : ℝ) * X.ψ θ))))) =
      Real.exp ((t : ℝ) * (X.ψ (θ - ε) - X.ψ θ)) := by
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
  have hLap := (X.laplace t (θ - ε) (sub_nonneg.mpr hεθ)).2
  calc
    (∫ ω, Real.exp (-ε * X.X t ω) ∂
      (P.withDensity (fun ω : Ω =>
        ENNReal.ofReal (Real.exp (θ * X.X t ω - (t : ℝ) * X.ψ θ))))) =
      ∫ ω, Real.exp (θ * X.X t ω - (t : ℝ) * X.ψ θ) *
        Real.exp (-ε * X.X t ω) ∂P := by
        rw [integral_withDensity_eq_integral_toReal_smul hmF hfin]
        apply integral_congr_ae
        filter_upwards [] with ω
        simp only [ENNReal.toReal_ofReal (Real.exp_nonneg _), smul_eq_mul]
    _ = ∫ ω, Real.exp (-(t : ℝ) * X.ψ θ) *
        Real.exp ((θ - ε) * X.X t ω) ∂P := by
        apply integral_congr_ae
        filter_upwards [] with ω
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
    _ = Real.exp (-(t : ℝ) * X.ψ θ) *
        ∫ ω, Real.exp ((θ - ε) * X.X t ω) ∂P :=
      integral_const_mul _ _
    _ = Real.exp ((t : ℝ) * (X.ψ (θ - ε) - X.ψ θ)) := by
      rw [hLap, ← Real.exp_add]
      congr 1
      change -(t : ℝ) * X.ψ θ + (t : ℝ) * X.ψ (θ - ε) =
        (t : ℝ) * (X.ψ (θ - ε) - X.ψ θ)
      ring
