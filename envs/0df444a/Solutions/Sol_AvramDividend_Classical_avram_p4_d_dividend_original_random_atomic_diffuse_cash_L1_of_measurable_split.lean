-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_d_dividend_original_random_atomic_diffuse_cash_L1_of_measurable_split
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T07:46:12.586385+00:00
-- url     : https://prove2.me/submissions/8e494d93-4311-49a6-ac05-2b078d2fa869

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x q : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (τ : Ω → ℝ≥0)
    (Cash : Ω → ℝ)
    (hCash : ∀ ω, Cash ω =
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
          ∂(dividendMeasure D ω)).toReal)
    (hCashI : Integrable Cash P)
    (μatom μdiffuse : Ω → Measure ℝ)
    (Atom Diffuse : Ω → ℝ)
    (hAtom : ∀ ω, Atom ω =
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
          ∂(μatom ω)).toReal)
    (hDiffuse : ∀ ω, Diffuse ω =
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
          ∂(μdiffuse ω)).toReal)
    (hRealSplit : ∀ᵐ ω ∂P, Cash ω = Atom ω + Diffuse ω)
    (hAtomMeas : AEStronglyMeasurable Atom P)
    (hDiffuseMeas : AEStronglyMeasurable Diffuse P) :
    Integrable Atom P ∧ Integrable Diffuse P := by
  have hAn : ∀ ω, 0 ≤ Atom ω := by
    intro ω
    rw [hAtom ω]
    exact ENNReal.toReal_nonneg
  have hDn : ∀ ω, 0 ≤ Diffuse ω := by
    intro ω
    rw [hDiffuse ω]
    exact ENNReal.toReal_nonneg
  have hAtomBound : ∀ᵐ ω ∂P, ‖Atom ω‖ ≤ ‖Cash ω‖ := by
    filter_upwards [hRealSplit] with ω hsplit
    have hc : 0 ≤ Cash ω := by
      rw [hsplit]
      exact add_nonneg (hAn ω) (hDn ω)
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (hAn ω), abs_of_nonneg hc, hsplit]
    linarith [hDn ω]
  have hDiffuseBound : ∀ᵐ ω ∂P, ‖Diffuse ω‖ ≤ ‖Cash ω‖ := by
    filter_upwards [hRealSplit] with ω hsplit
    have hc : 0 ≤ Cash ω := by
      rw [hsplit]
      exact add_nonneg (hAn ω) (hDn ω)
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (hDn ω), abs_of_nonneg hc, hsplit]
    linarith [hAn ω]
  exact ⟨Integrable.mono hCashI hAtomMeas hAtomBound,
    Integrable.mono hCashI hDiffuseMeas hDiffuseBound⟩
