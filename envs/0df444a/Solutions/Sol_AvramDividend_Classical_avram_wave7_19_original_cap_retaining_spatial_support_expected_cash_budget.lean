-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_19_original_cap_retaining_spatial_support_expected_cash_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T20:25:54.97099+00:00
-- url     : https://prove2.me/submissions/3425d0db-e12d-4ee2-ae76-e298d382d99e

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_19_original_boundary_preserved_monotone_interior_lintegral_iSup
import Theorems.Thm_AvramDividend_Classical_avram_wave7_19_original_spatial_localisation_ae_exhaustion_cash_budget
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
/-- Corrected source stopped Ito limit with all upper-cap Stieltjes cash retained. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q x T : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (boundary : Ω → Set ℝ) (interior : ℕ → Ω → Set ℝ)
    (hBoundaryMeas : ∀ ω, MeasurableSet (boundary ω))
    (hInteriorMeas : ∀ n ω, MeasurableSet (interior n ω))
    (hInteriorMon : ∀ ω, Monotone (fun n => interior n ω))
    (hCover : ∀ᵐ ω ∂P,
      paymentTimes (ruinTime X x D ω) ∩ Iic T ⊆
        ⋃ n : ℕ, boundary ω ∪ interior n ω)
    (hLocalCashMeas : ∀ n, Measurable (fun ω =>
      ∫⁻ t in boundary ω ∪ interior n ω,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)))
    (budget : ℝ≥0∞)
    (hBudget : ∀ n,
      (∫⁻ ω, (∫⁻ t in boundary ω ∪ interior n ω,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) ∂P) ≤ budget) :
    (∫⁻ ω, (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) ∂P) ≤ budget := by
  let L (n : ℕ) (ω : Ω) : ℝ≥0∞ :=
    ∫⁻ t in boundary ω ∪ interior n ω,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)
  have hLMon : ∀ ω, Monotone (fun n => L n ω) := by
    intro ω n m hnm
    dsimp [L]
    apply lintegral_mono_set
    intro t ht
    rcases ht with hb | hi
    · exact Or.inl hb
    · exact Or.inr (hInteriorMon ω hnm hi)
  have hExhaust : ∀ᵐ ω ∂P,
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) ≤
        ⨆ n : ℕ, L n ω := by
    filter_upwards [hCover] with ω hω
    exact avram_wave7_19_original_boundary_preserved_monotone_interior_lintegral_iSup
      X q x T D ω (boundary ω) (fun n => interior n ω)
      (hBoundaryMeas ω) (fun n => hInteriorMeas n ω) (hInteriorMon ω) hω
  exact avram_wave7_19_original_spatial_localisation_ae_exhaustion_cash_budget
    X q x T D hD L hLocalCashMeas hLMon hExhaust budget hBudget
