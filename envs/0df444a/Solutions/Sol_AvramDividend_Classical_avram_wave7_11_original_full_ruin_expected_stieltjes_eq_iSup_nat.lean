-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_11_original_full_ruin_expected_stieltjes_eq_iSup_nat
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T16:42:01.381324+00:00
-- url     : https://prove2.me/submissions/c58ee69c-ea50-4d9c-95f7-f04d6be2adf4

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_paymentTimes_min_mono_horizon
import Theorems.Thm_AvramDividend_Classical_avram_wave5_05_original_arbitrary_measurable_stop_complete_stieltjes_reward_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave7_11_ruin_clock_truncation_inner_lintegral_iSup

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Exact original-process expectation identity for natural ruin-clock
    exhaustions, retaining the full finite-horizon Stieltjes payout. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (q T : ℝ) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) =
    ⨆ n : ℕ, (∫⁻ ω, ∫⁻ t in
      paymentTimes (min (ruinTime X x D ω) (n : ℝ≥0∞)) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) := by
  let F : ℕ → Ω → ℝ≥0∞ := fun n ω =>
    ∫⁻ t in paymentTimes (min (ruinTime X x D ω) (n : ℝ≥0∞)) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)
  have hFmeas (n : ℕ) : Measurable (F n) :=
    avram_wave5_05_original_arbitrary_measurable_stop_complete_stieltjes_reward_measurable
      X x D hD q T (fun _ : Ω => (n : ℝ≥0∞)) measurable_const
  have hFmono : Monotone F := by
    intro n m hnm ω
    apply MeasureTheory.lintegral_mono_set
    intro t ht
    have hcast : (n : ℝ≥0∞) ≤ (m : ℝ≥0∞) := by exact_mod_cast hnm
    exact ⟨paymentTimes_min_mono_horizon
      (ruinTime X x D ω) _ _ hcast ht.1, ht.2⟩
  calc
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) =
      (∫⁻ ω, ⨆ n, F n ω ∂P) := by
        congr 1
        funext ω
        exact avram_wave7_11_ruin_clock_truncation_inner_lintegral_iSup
          D ω (ruinTime X x D ω) q T
    _ = ⨆ n, (∫⁻ ω, F n ω ∂P) := lintegral_iSup hFmeas hFmono
    _ = _ := rfl
