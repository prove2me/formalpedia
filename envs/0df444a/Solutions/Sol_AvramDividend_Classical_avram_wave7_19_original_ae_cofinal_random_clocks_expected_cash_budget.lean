-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_19_original_ae_cofinal_random_clocks_expected_cash_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T17:32:49.632851+00:00
-- url     : https://prove2.me/submissions/4b21f309-bf3d-40ad-8a02-39be4516b3a3

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_19_original_cofinal_random_clocks_full_cash_lintegral_iSup
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
/-- Almost-sure cofinal source clocks suffice for the full ruin cash expectation limit. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q x T : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (σ : ℕ → Ω → ℝ≥0∞)
    (hσ : ∀ ω : Ω, Monotone (fun k : ℕ => σ k ω))
    (hSup : ∀ᵐ ω ∂P, (⨆ k : ℕ, σ k ω) = ruinTime X x D ω)
    (hMeas : ∀ k : ℕ, Measurable (fun ω : Ω =>
      ∫⁻ t in paymentTimes (σ k ω) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)))
    (budget : ℝ≥0∞)
    (hBound : ∀ k : ℕ,
      (∫⁻ ω, (∫⁻ t in paymentTimes (σ k ω) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) ∂P) ≤ budget) :
    (∫⁻ ω, (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) ∂P) ≤ budget := by
  classical
  let f : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal (Real.exp (-(q * t)))
  let A (k : ℕ) (ω : Ω) : ℝ≥0∞ :=
    ∫⁻ t in paymentTimes (σ k ω) ∩ Iic T, f t ∂(dividendMeasure D ω)
  let B (ω : Ω) : ℝ≥0∞ :=
    ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      f t ∂(dividendMeasure D ω)
  have hpoint : ∀ᵐ ω ∂P, B ω = ⨆ k : ℕ, A k ω := by
    filter_upwards [hSup] with ω hω
    exact avram_wave7_19_original_cofinal_random_clocks_full_cash_lintegral_iSup
      X q x T D ω (fun k => σ k ω) (hσ ω) hω
  have hmono : Monotone A := by
    intro k l hkl ω
    change (∫⁻ t in paymentTimes (σ k ω) ∩ Iic T, f t ∂(dividendMeasure D ω)) ≤
      (∫⁻ t in paymentTimes (σ l ω) ∩ Iic T, f t ∂(dividendMeasure D ω))
    apply lintegral_mono_set
    intro t ht
    have hp : 0 ≤ t ∧ (t = 0 ∨ ENNReal.ofReal t < σ k ω) := ht.1
    refine ⟨?_, ht.2⟩
    change 0 ≤ t ∧ (t = 0 ∨ ENNReal.ofReal t < σ l ω)
    rcases hp.2 with hz | hlt
    · exact ⟨hp.1, Or.inl hz⟩
    · exact ⟨hp.1, Or.inr (lt_of_lt_of_le hlt (hσ ω hkl))⟩
  have hm : ∀ k : ℕ, Measurable (A k) := by
    intro k; exact hMeas k
  have hb : ∀ k : ℕ, (∫⁻ ω, A k ω ∂P) ≤ budget := by
    intro k; exact hBound k
  change (∫⁻ ω, B ω ∂P) ≤ budget
  calc
    (∫⁻ ω, B ω ∂P) ≤ ∫⁻ ω, ⨆ k : ℕ, A k ω ∂P := by
      apply lintegral_mono_ae
      filter_upwards [hpoint] with ω hω
      exact le_of_eq hω
    _ = ⨆ k : ℕ, (∫⁻ ω, A k ω ∂P) :=
      lintegral_iSup hm hmono
    _ ≤ budget := iSup_le hb
