-- Prove2me | solution 1 for AvramDividend.Classical.avram_f6_original_subclock_cash_integrable_of_finite_full_mass
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T10:57:46.774283+00:00
-- url     : https://prove2.me/submissions/4d1d4cde-7fca-4831-8537-0e63124a1822

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_f6_original_subclock_real_cash_dominated_if_full_finite
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x q : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (τ : Ω → ℝ≥0) (σ : ℕ → Ω → ℝ≥0)
    (hclock : ∀ k ω, σ k ω ≤ τ ω)
    (hFullFinite : ∀ ω : Ω,
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)) ≠ ⊤)
    (FullCash : Ω → ℝ)
    (hFullCash : ∀ ω, FullCash ω =
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal)
    (hFullI : Integrable FullCash P)
    (PartCash : ℕ → Ω → ℝ)
    (hPartCash : ∀ k ω, PartCash k ω =
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (σ k ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal)
    (hPartMeas : ∀ k, AEStronglyMeasurable (PartCash k) P) :
    ∀ k, Integrable (PartCash k) P := by
  intro k
  apply hFullI.mono' (hPartMeas k)
  filter_upwards [] with ω
  have hsub :=
    avram_f6_original_subclock_real_cash_dominated_if_full_finite
      X x q D τ σ hclock hFullFinite k ω
  have hp : 0 ≤ PartCash k ω := by
    rw [hPartCash k ω]
    exact ENNReal.toReal_nonneg
  have hf : 0 ≤ FullCash ω := by
    rw [hFullCash ω]
    exact ENNReal.toReal_nonneg
  have hle : PartCash k ω ≤ FullCash ω := by
    rw [hPartCash k ω, hFullCash ω]
    exact hsub
  simpa only [Real.norm_eq_abs, abs_of_nonneg hp, abs_of_nonneg hf] using hle
