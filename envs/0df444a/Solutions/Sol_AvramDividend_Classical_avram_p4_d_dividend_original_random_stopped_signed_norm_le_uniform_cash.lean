-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_d_dividend_original_random_stopped_signed_norm_le_uniform_cash
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T18:50:11.48186+00:00
-- url     : https://prove2.me/submissions/f48a3344-967c-44f7-afff-0ff6117e1f66

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_ubv_compact_interior_derivative_bound
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_random_stopped_uniform_band_kernel_bound
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_random_stopped_mass_le_uniform_horizon_cash
import Theorems.Thm_AvramDividend_Classical_paymentTimes_membership_to_nNReal_active
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_dividendMeasure_Icc_zero_eq_rightLimit

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
/-- Uniform, non-random constant times the actual random-stopped Cash
dominates the true source signed diffuse dividend remainder on every path. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (σ : Ω → ℝ≥0∞) (τ : Ω → ℝ≥0) (n : ℕ)
    (hτ : ∀ ω, τ ω ≤ (n : ℝ≥0))
    (ν : Ω → Measure ℝ)
    (hdom : ∀ ω, ν ω ≤ dividendMeasure D ω)
    (q : ℝ) (hq : 0 ≤ q) (C : ℝ≥0∞) (w : ℝ → ℝ)
    (hwC2 : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (a b : ℝ) (hab : a ≤ b)
    (hBand : Icc a b ⊆ {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hstate : ∀ ω, ∀ᵐ s ∂(ν ω).restrict
      (paymentTimes (σ ω) ∩ Iic (τ ω : ℝ)),
      x + Function.leftLim (fun r : ℝ≥0 => X.X r ω) s.toNNReal -
        rightLimit D s.toNNReal ω ∈ Icc a b) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ ω,
      ‖∫ s in (paymentTimes (σ ω) ∩ Iic (τ ω : ℝ)),
        Real.exp (-(q * s)) *
          (1 - deriv w (x + Function.leftLim (fun r : ℝ≥0 => X.X r ω)
            s.toNNReal - rightLimit D s.toNNReal ω)) ∂(ν ω)‖ ≤
        (1 + K) * Real.exp (q * (n : ℝ)) *
          (∫⁻ s in paymentTimes (σ ω) ∩ Iic (τ ω : ℝ),
            ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal := by
  obtain ⟨K, hK0, hK⟩ :=
    avram_p4_d_dividend_ubv_compact_interior_derivative_bound
      C w hwC2 a b hab hBand
  refine ⟨K, hK0, ?_⟩
  intro ω
  let S : Set ℝ := paymentTimes (σ ω) ∩ Iic (τ ω : ℝ)
  have hsubset : S ⊆ Icc (0 : ℝ) (τ ω : ℝ) := by
    intro u hu
    exact ⟨(paymentTimes_membership_to_nNReal_active (σ ω) u hu.1).1, hu.2⟩
  have hmass : (ν ω) S < ⊤ := by
    calc
      (ν ω) S ≤ (dividendMeasure D ω) S := hdom ω S
      _ ≤ (dividendMeasure D ω) (Icc (0 : ℝ) (τ ω : ℝ)) := measure_mono hsubset
      _ = ENNReal.ofReal (rightLimit D (τ ω) ω) :=
        avram_wave3_03_dividendMeasure_Icc_zero_eq_rightLimit D hD ω (τ ω)
      _ < ⊤ := ENNReal.ofReal_lt_top
  have hkernel :=
    avram_p4_d_dividend_original_random_stopped_uniform_band_kernel_bound
      X x D hD σ τ ν q hq w a b K hK0 hK hstate ω
  have hnorm := norm_setIntegral_le_of_norm_le_const_ae hmass hkernel
  have hcash :=
    avram_p4_d_dividend_original_random_stopped_mass_le_uniform_horizon_cash
      D hD σ τ n hτ ν hdom q hq ω
  calc
    _ ≤ (1 + K) * (ν ω).real S := hnorm
    _ ≤ (1 + K) * (Real.exp (q * (n : ℝ)) *
        (∫⁻ s in S, ENNReal.ofReal (Real.exp (-(q * s)))
          ∂(dividendMeasure D ω)).toReal) :=
      mul_le_mul_of_nonneg_left hcash (by linarith)
    _ = (1 + K) * Real.exp (q * (n : ℝ)) *
        (∫⁻ s in S, ENNReal.ofReal (Real.exp (-(q * s)))
          ∂(dividendMeasure D ω)).toReal := by ring
