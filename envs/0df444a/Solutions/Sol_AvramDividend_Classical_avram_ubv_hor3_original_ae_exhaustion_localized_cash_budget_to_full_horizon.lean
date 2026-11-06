-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_hor3_original_ae_exhaustion_localized_cash_budget_to_full_horizon
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T16:55:40.569366+00:00
-- url     : https://prove2.me/submissions/2a3c8d44-8ef3-47ad-ab2e-93156e09f9f8

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x q T : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (Cash : Ω → ℝ≥0∞)
    (hCash : ∀ ω, Cash ω =
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)))
    (hCashMeas : Measurable Cash)
    (A : ℕ → Set Ω)
    (hAmeas : ∀ k, MeasurableSet (A k))
    (hAmono : Monotone A)
    (hAcover : ∀ᵐ ω ∂P, ∃ k, ω ∈ A k)
    (budget : ℝ≥0∞)
    (hLocalized : ∀ k,
      (∫⁻ ω in A k, Cash ω ∂P) ≤ budget) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
      budget := by
  let Ck : ℕ → Ω → ℝ≥0∞ := fun k ω => (A k).indicator Cash ω
  have hCkMeas : ∀ k, Measurable (Ck k) := by
    intro k
    exact hCashMeas.indicator (hAmeas k)
  have hCkMono : Monotone Ck := by
    intro k l hkl ω
    by_cases hk : ω ∈ A k
    · have hl : ω ∈ A l := hAmono hkl hk
      simp [Ck, hk, hl]
    · simp [Ck, hk]
  have hSup : ∀ᵐ ω ∂P, (⨆ k, Ck k ω) = Cash ω := by
    filter_upwards [hAcover] with ω hcover
    obtain ⟨k, hk⟩ := hcover
    apply le_antisymm
    · apply iSup_le
      intro j
      by_cases hj : ω ∈ A j <;> simp [Ck, hj]
    · calc
        Cash ω = Ck k ω := by simp [Ck, hk]
        _ ≤ ⨆ j, Ck j ω := le_iSup_of_le k le_rfl
  have hEach (k : ℕ) : (∫⁻ ω, Ck k ω ∂P) ≤ budget := by
    change (∫⁻ ω, (A k).indicator Cash ω ∂P) ≤ budget
    rw [lintegral_indicator (hAmeas k) Cash]
    exact hLocalized k
  have hBound : (∫⁻ ω, Cash ω ∂P) ≤ budget := by
    calc
      (∫⁻ ω, Cash ω ∂P) = (∫⁻ ω, (⨆ k, Ck k ω) ∂P) :=
        (lintegral_congr_ae hSup).symm
      _ = ⨆ k, (∫⁻ ω, Ck k ω ∂P) := lintegral_iSup hCkMeas hCkMono
      _ ≤ budget := iSup_le hEach
  simpa only [hCash] using hBound
