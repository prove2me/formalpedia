-- Prove2me | solution 1 for AvramDividend.Classical.avram_limit2_original_positive_strict_terminal_to_real_perpetual_L1_exact
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T18:20:44.902542+00:00
-- url     : https://prove2.me/submissions/5478b547-137a-4095-a0ef-508d4c1a80b2

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_limit2_original_positive_strict_terminal_budget_to_perpetual_dividendValue
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_perpetual_signed_stieltjes_L1_and_exact_outer_mean_of_finite
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissible X x D)
    (B : ℝ≥0∞) (hB : B < ⊤)
    (Terminal : ℝ → Ω → ℝ≥0∞)
    (hPositive : ∀ (T : ℝ), 0 < T →
      (∫⁻ ω, ((∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Set.Iio T,
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)) + Terminal T ω) ∂P) ≤ B) :
    (Integrable (fun ω : Ω =>
      ∫ t in paymentTimes (ruinTime X x D ω),
        Real.exp (-(q * t)) ∂(dividendMeasure D ω)) P ∧
    dividendValue X q x D =
      ENNReal.ofReal
        (∫ ω, (∫ t in paymentTimes (ruinTime X x D ω),
          Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ∂P)) ∧
    dividendValue X q x D ≤ B := by
  have hValue : dividendValue X q x D ≤ B :=
    avram_limit2_original_positive_strict_terminal_budget_to_perpetual_dividendValue
      X q x D hD B Terminal hPositive
  have hFinite : dividendValue X q x D < ⊤ :=
    lt_of_le_of_lt hValue hB
  exact ⟨avram_wave7_03_original_perpetual_signed_stieltjes_L1_and_exact_outer_mean_of_finite
    X x D hD.1 q hFinite, hValue⟩
