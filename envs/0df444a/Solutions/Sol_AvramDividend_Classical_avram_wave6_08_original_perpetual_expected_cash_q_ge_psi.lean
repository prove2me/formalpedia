-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_08_original_perpetual_expected_cash_q_ge_psi
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T00:10:46.215809+00:00
-- url     : https://prove2.me/submissions/cbd30b1e-15ee-4bed-a70b-7fe2c0c3a403

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_03_original_stopped_fullStieltjes_realDiscount_q_ge_psi_payoff_le_expCapital
import Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_random_upper_clock_complete_stieltjes_cash_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave6_08_original_perpetual_stieltjes_cash_measurable
import Theorems.Thm_AvramDividend_Classical_paymentTimes_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave6_08_original_perpetual_cash_eq_iSup_integer_truncations
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : X.ψ 1 ≤ q) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂dividendMeasure D ω ∂P) ≤
      ENNReal.ofReal (Real.exp x) := by
  classical
  let W : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal (Real.exp (-(q * t)))
  let E : ℕ → Ω → Set ℝ := fun n ω =>
    paymentTimes (ruinTime X x D ω) ∩ Iic (((n + 1 : ℕ) : ℝ))
  let F : ℕ → Ω → ℝ≥0∞ := fun n ω =>
    ∫⁻ t in E n ω, W t ∂dividendMeasure D ω
  let B : Ω → ℝ≥0∞ := fun ω =>
    ∫⁻ t in paymentTimes (ruinTime X x D ω), W t ∂dividendMeasure D ω
  have hFm (n : ℕ) : Measurable (F n) := by
    have h := avram_wave6_06_original_random_upper_clock_complete_stieltjes_cash_measurable
      X x D hD.1.1 q (fun _ : Ω => (((n + 1 : ℕ) : ℝ))) measurable_const
    simpa only [F, E, W] using h
  have hFmono : Monotone F := by
    intro n m hnm ω
    apply lintegral_mono_set
    intro t ht
    have hcast : (((n + 1 : ℕ) : ℝ)) ≤ (((m + 1 : ℕ) : ℝ)) := by
      exact_mod_cast Nat.add_le_add_right hnm 1
    exact ⟨ht.1, le_trans ht.2 hcast⟩
  have hFb (n : ℕ) :
      (∫⁻ ω, F n ω ∂P) ≤ ENNReal.ofReal (Real.exp x) := by
    have h :=
      avram_wave4_03_original_stopped_fullStieltjes_realDiscount_q_ge_psi_payoff_le_expCapital
        X x C D hD q hq (((n + 1 : ℕ) : ℝ≥0)) (by positivity)
    simpa only [F, E, W, NNReal.coe_natCast] using h
  have hFsup (ω : Ω) : B ω = ⨆ n : ℕ, F n ω := by
    simpa only [B, F, E, W] using
      (avram_wave6_08_original_perpetual_cash_eq_iSup_integer_truncations
        X x D hD.1.1 q ω)
  calc
    (∫⁻ ω, B ω ∂P) = (∫⁻ ω, ⨆ n : ℕ, F n ω ∂P) :=
      lintegral_congr hFsup
    _ = ⨆ n : ℕ, ∫⁻ ω, F n ω ∂P := lintegral_iSup hFm hFmono
    _ ≤ ENNReal.ofReal (Real.exp x) := iSup_le hFb
