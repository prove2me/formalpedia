-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_11_original_expected_positive_horizon_exact_endpoint_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T19:11:51.366259+00:00
-- url     : https://prove2.me/submissions/1137a5e6-4afa-4601-9df3-b8fe4a803217

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_11_positive_horizon_reward_eq_truncated_clock_plus_endpoint
import Theorems.Thm_AvramDividend_Classical_avram_wave5_05_original_arbitrary_measurable_stop_complete_stieltjes_reward_measurable
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Analysis.Complex.Exponential

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Exact original-probability finite-horizon discounted expected cash
    equals strict clock-truncated cash plus the true horizon Stieltjes atom. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (q T : ℝ) (hT : 0 < T) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) =
    (∫⁻ ω, ∫⁻ t in
      paymentTimes (min (ruinTime X x D ω) (ENNReal.ofReal T)) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) +
    (∫⁻ ω, ∫⁻ t in
      (paymentTimes (ruinTime X x D ω) ∩ Iic T) ∩ {T},
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) := by
  have hF : Measurable (fun ω : Ω =>
      ∫⁻ t in paymentTimes
        (min (ruinTime X x D ω) (ENNReal.ofReal T)) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) :=
    avram_wave5_05_original_arbitrary_measurable_stop_complete_stieltjes_reward_measurable
      X x D hD q T (fun _ : Ω => ENNReal.ofReal T) measurable_const
  calc
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) =
      (∫⁻ ω,
        (∫⁻ t in
          paymentTimes (min (ruinTime X x D ω) (ENNReal.ofReal T)) ∩ Iic T,
          ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) +
        (∫⁻ t in (paymentTimes (ruinTime X x D ω) ∩ Iic T) ∩ {T},
          ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) ∂P) := by
            apply lintegral_congr
            intro ω
            exact avram_wave7_11_positive_horizon_reward_eq_truncated_clock_plus_endpoint
              D ω (ruinTime X x D ω) q T hT
    _ = (∫⁻ ω, ∫⁻ t in
        paymentTimes (min (ruinTime X x D ω) (ENNReal.ofReal T)) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) +
      (∫⁻ ω, ∫⁻ t in (paymentTimes (ruinTime X x D ω) ∩ Iic T) ∩ {T},
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) :=
          lintegral_add_left hF (fun ω : Ω =>
            ∫⁻ t in (paymentTimes (ruinTime X x D ω) ∩ Iic T) ∩ {T},
              ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω))