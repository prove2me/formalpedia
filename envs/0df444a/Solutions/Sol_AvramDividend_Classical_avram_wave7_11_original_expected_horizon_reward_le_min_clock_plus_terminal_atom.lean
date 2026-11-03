-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_11_original_expected_horizon_reward_le_min_clock_plus_terminal_atom
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T18:47:08.766207+00:00
-- url     : https://prove2.me/submissions/5d56e39c-cb46-493e-bdd0-ff147070d01c

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_11_horizon_reward_le_truncated_clock_plus_endpoint
import Theorems.Thm_AvramDividend_Classical_avram_wave5_05_original_arbitrary_measurable_stop_complete_stieltjes_reward_measurable
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Lift exact original-path endpoint decomposition to the genuine
    probability expectation without discarding any terminal dividend atom. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (q T : ℝ) (hT : 0 ≤ T) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
    (∫⁻ ω, ∫⁻ t in
      paymentTimes (min (ruinTime X x D ω) (ENNReal.ofReal T)) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) +
    (∫⁻ ω, ∫⁻ t in
      (paymentTimes (ruinTime X x D ω) ∩ Iic T) ∩ {T},
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) := by
  have hF :
      Measurable (fun ω : Ω =>
        ∫⁻ t in paymentTimes (min (ruinTime X x D ω) (ENNReal.ofReal T)) ∩ Iic T,
          ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) :=
    avram_wave5_05_original_arbitrary_measurable_stop_complete_stieltjes_reward_measurable
      X x D hD q T (fun _ : Ω => ENNReal.ofReal T) measurable_const
  calc
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
      (∫⁻ ω,
        (∫⁻ t in
          paymentTimes (min (ruinTime X x D ω) (ENNReal.ofReal T)) ∩ Iic T,
          ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) +
        (∫⁻ t in (paymentTimes (ruinTime X x D ω) ∩ Iic T) ∩ {T},
          ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) ∂P) := by
          apply MeasureTheory.lintegral_mono
          intro ω
          exact avram_wave7_11_horizon_reward_le_truncated_clock_plus_endpoint
            D ω (ruinTime X x D ω) q T hT
    _ = (∫⁻ ω, ∫⁻ t in
        paymentTimes (min (ruinTime X x D ω) (ENNReal.ofReal T)) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) +
      (∫⁻ ω, ∫⁻ t in (paymentTimes (ruinTime X x D ω) ∩ Iic T) ∩ {T},
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) :=
          lintegral_add_left hF (fun ω : Ω =>
            ∫⁻ t in (paymentTimes (ruinTime X x D ω) ∩ Iic T) ∩ {T},
              ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω))