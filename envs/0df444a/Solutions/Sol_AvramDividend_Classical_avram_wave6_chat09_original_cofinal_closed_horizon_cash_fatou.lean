-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_chat09_original_cofinal_closed_horizon_cash_fatou
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T08:52:28.391819+00:00
-- url     : https://prove2.me/submissions/6f9cfa3c-9761-47d9-8c92-1f39072f03d3

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_random_upper_clock_complete_stieltjes_cash_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Source-faithful closed-horizon cash bound from increasing random
localisers, retaining the terminal right-payment atom. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (q T : ℝ) (τ : ℕ → Ω → ℝ)
    (hτm : ∀ n, Measurable (τ n))
    (hτmono : ∀ ω, Monotone (fun n => τ n ω))
    (hcofinal : ∀ᵐ ω ∂P, ∃ n, T ≤ τ n ω)
    (B : ℝ≥0∞)
    (hbound : ∀ n,
      (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (τ n ω),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂dividendMeasure D ω ∂P) ≤ B) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂dividendMeasure D ω ∂P) ≤ B := by
  let F : ℕ → Ω → ℝ≥0∞ := fun n ω =>
    ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (τ n ω),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂dividendMeasure D ω
  have hFm (n : ℕ) : Measurable (F n) := by
    dsimp [F]
    exact avram_wave6_06_original_random_upper_clock_complete_stieltjes_cash_measurable
      X x D hD q (τ n) (hτm n)
  have hFmono : Monotone F := by
    intro n m hnm ω
    dsimp [F]
    apply lintegral_mono_set
    intro t ht
    exact ⟨ht.1, le_trans ht.2 (hτmono ω hnm)⟩
  have hLe : ∀ᵐ ω ∂P,
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂dividendMeasure D ω) ≤
        ⨆ n, F n ω := by
    filter_upwards [hcofinal] with ω hω
    obtain ⟨n, hn⟩ := hω
    calc
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
          ENNReal.ofReal (Real.exp (-(q * t))) ∂dividendMeasure D ω)
          ≤ F n ω := by
            dsimp [F]
            apply lintegral_mono_set
            intro t ht
            exact ⟨ht.1, le_trans ht.2 hn⟩
      _ ≤ ⨆ m, F m ω := le_iSup (fun m => F m ω) n
  have hBoundF (n : ℕ) : (∫⁻ ω, F n ω ∂P) ≤ B := by
    simpa only [F] using hbound n
  calc
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂dividendMeasure D ω ∂P)
        ≤ (∫⁻ ω, ⨆ n, F n ω ∂P) := lintegral_mono_ae hLe
    _ = ⨆ n, (∫⁻ ω, F n ω ∂P) := lintegral_iSup hFm hFmono
    _ ≤ B := iSup_le hBoundF
