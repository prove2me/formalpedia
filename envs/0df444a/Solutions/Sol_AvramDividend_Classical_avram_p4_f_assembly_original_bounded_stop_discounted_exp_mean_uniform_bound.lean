-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f_assembly_original_bounded_stop_discounted_exp_mean_uniform_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T21:39:24.440639+00:00
-- url     : https://prove2.me/submissions/abc5690f-af7a-49fe-9191-1901092473a8

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_rightCont_bounded_stop_esscher_likelihood_mean_one
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- All bounded original stopping clocks obey the same exponential moment bound. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ : ℝ) (hθ : 0 ≤ θ) (q : ℝ)
    (τ : Ω → ℝ≥0)
    (hstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (H : ℝ≥0) (hbound : ∀ ω, τ ω ≤ H) :
    (∫ ω, Real.exp (θ * X.X (τ ω) ω - (τ ω : ℝ) * q) ∂P) ≤
      Real.exp (|X.ψ θ - q| * (H : ℝ)) := by
  have hmean :=
    avram_p4_f_assembly_original_rightCont_bounded_stop_esscher_likelihood_mean_one
      X θ hθ τ hstop H hbound
  have hgi : Integrable
      (fun ω => Real.exp (θ * X.X (τ ω) ω - (τ ω : ℝ) * X.ψ θ)) P :=
    integrable_of_integral_eq_one hmean
  let M : ℝ := Real.exp (|X.ψ θ - q| * (H : ℝ))
  have hmajor : Integrable
      (fun ω => M * Real.exp
        (θ * X.X (τ ω) ω - (τ ω : ℝ) * X.ψ θ)) P :=
    hgi.const_mul M
  have hminorNonneg : ∀ᵐ ω ∂P,
      0 ≤ Real.exp (θ * X.X (τ ω) ω - (τ ω : ℝ) * q) :=
    Filter.Eventually.of_forall (fun ω => le_of_lt (Real.exp_pos _))
  have hBound : ∀ ω, Real.exp
      (θ * X.X (τ ω) ω - (τ ω : ℝ) * q) ≤
      M * Real.exp (θ * X.X (τ ω) ω - (τ ω : ℝ) * X.ψ θ) := by
    intro ω
    have hτnonneg : (0 : ℝ) ≤ (τ ω : ℝ) := NNReal.coe_nonneg _
    have hτH : (τ ω : ℝ) ≤ (H : ℝ) := by exact_mod_cast hbound ω
    have hcoef : X.ψ θ - q ≤ |X.ψ θ - q| := le_abs_self _
    have ha : (X.ψ θ - q) * (τ ω : ℝ) ≤
        |X.ψ θ - q| * (τ ω : ℝ) :=
      mul_le_mul_of_nonneg_right hcoef hτnonneg
    have hb : |X.ψ θ - q| * (τ ω : ℝ) ≤
        |X.ψ θ - q| * (H : ℝ) :=
      mul_le_mul_of_nonneg_left hτH (abs_nonneg _)
    have he := Real.exp_le_exp.mpr (ha.trans hb)
    have hExpEq : Real.exp (θ * X.X (τ ω) ω - (τ ω : ℝ) * q) =
        Real.exp (θ * X.X (τ ω) ω - (τ ω : ℝ) * X.ψ θ) *
          Real.exp ((X.ψ θ - q) * (τ ω : ℝ)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    calc
      Real.exp (θ * X.X (τ ω) ω - (τ ω : ℝ) * q) =
          Real.exp (θ * X.X (τ ω) ω - (τ ω : ℝ) * X.ψ θ) *
            Real.exp ((X.ψ θ - q) * (τ ω : ℝ)) := hExpEq
      _ ≤ Real.exp (θ * X.X (τ ω) ω - (τ ω : ℝ) * X.ψ θ) * M :=
        mul_le_mul_of_nonneg_left he (le_of_lt (Real.exp_pos _))
      _ = M * Real.exp (θ * X.X (τ ω) ω - (τ ω : ℝ) * X.ψ θ) :=
        mul_comm _ _
  calc
    (∫ ω, Real.exp (θ * X.X (τ ω) ω - (τ ω : ℝ) * q) ∂P) ≤
        ∫ ω, M * Real.exp
          (θ * X.X (τ ω) ω - (τ ω : ℝ) * X.ψ θ) ∂P :=
      integral_mono_of_nonneg hminorNonneg hmajor
        (Filter.Eventually.of_forall hBound)
    _ = M * (∫ ω, Real.exp
          (θ * X.X (τ ω) ω - (τ ω : ℝ) * X.ψ θ) ∂P) := by
      rw [integral_const_mul]
    _ = M := by rw [hmean, mul_one]
    _ = Real.exp (|X.ψ θ - q| * (H : ℝ)) := rfl
