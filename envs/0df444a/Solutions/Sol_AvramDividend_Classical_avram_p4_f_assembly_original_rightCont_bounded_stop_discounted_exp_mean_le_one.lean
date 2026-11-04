-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f_assembly_original_rightCont_bounded_stop_discounted_exp_mean_le_one
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T21:13:33.08955+00:00
-- url     : https://prove2.me/submissions/1488f0a2-8bb1-4556-8ff1-9d07fb00f4c0

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_rightCont_bounded_stop_esscher_likelihood_mean_one
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The exact stopped source exponential is a discounted expectation envelope. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ : ℝ) (hθ : 0 ≤ θ) (q : ℝ) (hq : X.ψ θ ≤ q)
    (τ : Ω → ℝ≥0)
    (hstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (H : ℝ≥0) (hbound : ∀ ω, τ ω ≤ H) :
    (∫ ω, Real.exp (θ * X.X (τ ω) ω - (τ ω : ℝ) * q) ∂P) ≤ (1 : ℝ) := by
  have hmean :=
    avram_p4_f_assembly_original_rightCont_bounded_stop_esscher_likelihood_mean_one
      X θ hθ τ hstop H hbound
  have hgi : Integrable
      (fun ω => Real.exp (θ * X.X (τ ω) ω - (τ ω : ℝ) * X.ψ θ)) P :=
    integrable_of_integral_eq_one hmean
  have hn : ∀ᵐ ω ∂P,
      (0 : ℝ) ≤ Real.exp (θ * X.X (τ ω) ω - (τ ω : ℝ) * q) :=
    Filter.Eventually.of_forall (fun ω => (Real.exp_pos _).le)
  have hle : ∀ᵐ ω ∂P,
      Real.exp (θ * X.X (τ ω) ω - (τ ω : ℝ) * q) ≤
      Real.exp (θ * X.X (τ ω) ω - (τ ω : ℝ) * X.ψ θ) := by
    filter_upwards [] with ω
    apply Real.exp_le_exp.mpr
    have ht : (0 : ℝ) ≤ (τ ω : ℝ) := NNReal.coe_nonneg _
    have hmul := mul_le_mul_of_nonneg_left hq ht
    linarith
  calc
    (∫ ω, Real.exp (θ * X.X (τ ω) ω - (τ ω : ℝ) * q) ∂P) ≤
      ∫ ω, Real.exp (θ * X.X (τ ω) ω -
        (τ ω : ℝ) * X.ψ θ) ∂P :=
      integral_mono_of_nonneg hn hgi hle
    _ = 1 := hmean
