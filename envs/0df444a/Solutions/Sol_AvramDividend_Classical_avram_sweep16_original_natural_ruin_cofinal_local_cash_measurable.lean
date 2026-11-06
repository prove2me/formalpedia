-- Prove2me | solution 1 for AvramDividend.Classical.avram_sweep16_original_natural_ruin_cofinal_local_cash_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T18:07:58.099207+00:00
-- url     : https://prove2.me/submissions/bad2255a-4fae-4e07-8fad-92012399454e

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_ruinTime_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_random_upper_clock_complete_stieltjes_cash_measurable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (n : ℕ)
    (S : ℕ → Ω → ℝ≥0∞)
    (hSstop : ∀ k, IsStoppingTime 𝓕.rightCont (S k)) :
    ∀ k : ℕ, Measurable (fun ω =>
      ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
        Iic (((min (min (ruinTime X x D ω) (n : ℝ≥0∞)) (S k ω)).toNNReal : ℝ)),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) := by
  intro k
  have hRuin : Measurable (ruinTime X x D) :=
    ruinTime_measurable X x D hD.1.1
  have hSM : Measurable (S k) := (hSstop k).measurable'
  have hMin : Measurable (fun ω =>
      min (min (ruinTime X x D ω) (n : ℝ≥0∞)) (S k ω)) :=
    (hRuin.min measurable_const).min hSM
  have hTNN : Measurable (fun ω =>
      (min (min (ruinTime X x D ω) (n : ℝ≥0∞)) (S k ω)).toNNReal) :=
    ENNReal.measurable_toNNReal.comp hMin
  have hTReal : Measurable (fun ω =>
      ((min (min (ruinTime X x D ω) (n : ℝ≥0∞)) (S k ω)).toNNReal : ℝ)) :=
    measurable_coe_nnreal_real.comp hTNN
  exact avram_wave6_06_original_random_upper_clock_complete_stieltjes_cash_measurable
    X x D hD.1.1 q _ hTReal
