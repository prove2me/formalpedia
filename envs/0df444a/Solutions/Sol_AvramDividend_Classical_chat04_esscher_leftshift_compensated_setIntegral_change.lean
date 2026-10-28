-- Prove2me | solution 1 for AvramDividend.Classical.chat04_esscher_leftshift_compensated_setIntegral_change
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T21:30:08.404116+00:00
-- url     : https://prove2.me/submissions/8613d0be-97f5-493b-9210-51f47401652c

import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Probability.Process.Adapted
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic.Ring
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (t : ℝ≥0) (θ ε : ℝ)
    (A : Set Ω) (hA : MeasurableSet A) :
    (∫ ω in A,
      Real.exp (-ε * X.X t ω -
        (t : ℝ) * (X.ψ (θ - ε) - X.ψ θ)) ∂
      (P.withDensity (fun ω : Ω =>
        ENNReal.ofReal (Real.exp (θ * X.X t ω - (t : ℝ) * X.ψ θ))))) =
    (∫ ω in A,
      Real.exp ((θ - ε) * X.X t ω -
        (t : ℝ) * X.ψ (θ - ε)) ∂P) := by
  have hmX : Measurable (X.X t) := X.adapted.measurable
  have hmReal : Measurable (fun ω : Ω =>
      Real.exp (θ * X.X t ω - (t : ℝ) * X.ψ θ)) :=
    Real.continuous_exp.measurable.comp
      ((measurable_const.mul hmX).sub measurable_const)
  have hmF : Measurable (fun ω : Ω =>
      ENNReal.ofReal (Real.exp (θ * X.X t ω - (t : ℝ) * X.ψ θ))) :=
    ENNReal.measurable_ofReal.comp hmReal
  have hfin : ∀ᵐ ω ∂P.restrict A,
      ENNReal.ofReal (Real.exp (θ * X.X t ω - (t : ℝ) * X.ψ θ)) < ∞ :=
    Filter.Eventually.of_forall (fun ω => ENNReal.ofReal_lt_top)
  calc
    (∫ ω in A,
      Real.exp (-ε * X.X t ω -
        (t : ℝ) * (X.ψ (θ - ε) - X.ψ θ)) ∂
      (P.withDensity (fun ω : Ω =>
        ENNReal.ofReal (Real.exp (θ * X.X t ω - (t : ℝ) * X.ψ θ))))) =
      ∫ ω in A, Real.exp (θ * X.X t ω - (t : ℝ) * X.ψ θ) *
        Real.exp (-ε * X.X t ω -
          (t : ℝ) * (X.ψ (θ - ε) - X.ψ θ)) ∂P := by
        rw [setIntegral_withDensity_eq_setIntegral_toReal_smul hmF hfin _ hA]
        apply integral_congr_ae
        filter_upwards [] with ω
        simp only [ENNReal.toReal_ofReal (Real.exp_nonneg _), smul_eq_mul]
    _ = ∫ ω in A,
        Real.exp ((θ - ε) * X.X t ω - (t : ℝ) * X.ψ (θ - ε)) ∂P := by
        apply integral_congr_ae
        filter_upwards [] with ω
        rw [← Real.exp_add]
        congr 1
        ring
