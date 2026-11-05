-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_d_dividend_original_random_stopped_mass_le_uniform_horizon_cash
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T18:46:33.154485+00:00
-- url     : https://prove2.me/submissions/2ae095b9-5014-4913-b842-7d7ac15c2799

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_stopped_dominated_real_mass_le_cash

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
/-- The genuine source Cash uniformly dominates a random ruin-stopped
Stieltjes submeasure mass at any random clock below the fixed horizon n. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (σ : Ω → ℝ≥0∞) (τ : Ω → ℝ≥0) (n : ℕ)
    (hτ : ∀ ω, τ ω ≤ (n : ℝ≥0))
    (ν : Ω → Measure ℝ)
    (hdom : ∀ ω, ν ω ≤ dividendMeasure D ω)
    (q : ℝ) (hq : 0 ≤ q) :
    ∀ ω, (ν ω).real (paymentTimes (σ ω) ∩ Iic (τ ω : ℝ)) ≤
      Real.exp (q * (n : ℝ)) *
        (∫⁻ s in paymentTimes (σ ω) ∩ Iic (τ ω : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal := by
  intro ω
  let S : Set ℝ := paymentTimes (σ ω) ∩ Iic (τ ω : ℝ)
  let Cash : ℝ≥0∞ :=
    ∫⁻ s in S, ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)
  have hqτ : q * (τ ω : ℝ) ≤ q * (n : ℝ) := by
    apply mul_le_mul_of_nonneg_left _ hq
    exact_mod_cast (hτ ω)
  have hexp : Real.exp (q * (τ ω : ℝ)) ≤ Real.exp (q * (n : ℝ)) :=
    Real.exp_le_exp.mpr hqτ
  have hreal :=
    avram_p4_d_dividend_original_stopped_dominated_real_mass_le_cash
      D hD ω (σ ω) (τ ω) (ν ω) (hdom ω) q hq
  change (ν ω).real S ≤ Cash.toReal / Real.exp (-(q * (τ ω : ℝ))) at hreal
  calc
    (ν ω).real S ≤ Cash.toReal / Real.exp (-(q * (τ ω : ℝ))) := hreal
    _ = Real.exp (q * (τ ω : ℝ)) * Cash.toReal := by
      rw [Real.exp_neg, div_eq_mul_inv, inv_inv]
      ring
    _ ≤ Real.exp (q * (n : ℝ)) * Cash.toReal :=
      mul_le_mul_of_nonneg_right hexp ENNReal.toReal_nonneg
