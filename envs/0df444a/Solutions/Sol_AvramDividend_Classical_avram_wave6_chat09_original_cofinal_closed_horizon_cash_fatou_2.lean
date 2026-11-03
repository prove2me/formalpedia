-- Prove2me | solution 2 for AvramDividend.Classical.avram_wave6_chat09_original_cofinal_closed_horizon_cash_fatou
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T08:53:25.753911+00:00
-- url     : https://prove2.me/submissions/88e0afc8-ef25-4f5b-b988-1a6b622a5b6c

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_random_upper_clock_complete_stieltjes_cash_measurable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter
open scoped NNReal ENNReal
open AvramDividend.Classical

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
  let F : (Ω → ℝ) → Ω → ℝ≥0∞ := fun clock ω =>
    ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (clock ω),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂dividendMeasure D ω
  have hMeas (n : ℕ) : Measurable (F (τ n)) := by
    exact avram_wave6_06_original_random_upper_clock_complete_stieltjes_cash_measurable
      X x D hD q (τ n) (hτm n)
  have hSetMono (ω : Ω) (a b : ℝ) (hab : a ≤ b) :
      F (fun _ => a) ω ≤ F (fun _ => b) ω := by
    dsimp [F]
    apply lintegral_mono_set
    intro t ht
    exact ⟨ht.1, le_trans ht.2 hab⟩
  have hMono : Monotone (fun n : ℕ => F (τ n)) := by
    intro n m hnm ω
    exact hSetMono ω (τ n ω) (τ m ω) (hτmono ω hnm)
  have hPoint : ∀ᵐ ω ∂P,
      F (fun _ => T) ω ≤ ⨆ n : ℕ, F (τ n) ω := by
    filter_upwards [hcofinal] with ω hω
    obtain ⟨n, hn⟩ := hω
    exact (hSetMono ω T (τ n ω) hn).trans (le_iSup (fun j : ℕ => F (τ j) ω) n)
  have hBeppo :
      (∫⁻ ω, ⨆ n : ℕ, F (τ n) ω ∂P) =
        ⨆ n : ℕ, (∫⁻ ω, F (τ n) ω ∂P) :=
    lintegral_iSup hMeas hMono
  have hUpper : (⨆ n : ℕ, (∫⁻ ω, F (τ n) ω ∂P)) ≤ B := by
    exact iSup_le (fun n => hbound n)
  change (∫⁻ ω, F (fun _ => T) ω ∂P) ≤ B
  exact (lintegral_mono_ae hPoint).trans (hBeppo.le.trans hUpper)
