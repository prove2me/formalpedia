-- Prove2me | solution 1 for AvramDividend.Classical.avram_gledger107_original_ruinclipped_mesh_error_pointwise_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T13:07:54.1352+00:00
-- url     : https://prove2.me/submissions/ac38d66f-7c2f-4f88-a6c7-b8904539347b

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gledger105_original_clipped_strict_strip_le_real_strip
import Theorems.Thm_AvramDividend_Classical_avram_gledger106_original_ruinclipped_strict_mass_le_cash
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The strict physical final interval is pointwise dominated by the real-mesh envelope. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (q : ℝ) (hq : 0 ≤ q) (n ρ δ : ℝ≥0)
    (hρn : ρ ≤ n) (hρruin : (ρ : ℝ≥0∞) ≤ ruinTime X x D ω) :
    q * (δ : ℝ) * (dividendMeasure D ω (Ioo (0 : ℝ) (ρ : ℝ))).toReal +
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
        Ioo ((ρ - δ : ℝ≥0) : ℝ) (ρ : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal ≤
    q * (δ : ℝ) * Real.exp (q * (n : ℝ)) *
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (ρ : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
        Ioo ((ρ : ℝ) - (δ : ℝ)) (ρ : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal := by
  have hm := avram_gledger106_original_ruinclipped_strict_mass_le_cash
    X x D hD ω q hq n ρ hρn hρruin
  have ht := avram_gledger105_original_clipped_strict_strip_le_real_strip
    X x D hD ω q hq n ρ δ hρn
  have hc : 0 ≤ q * (δ : ℝ) := by positivity
  have hh := add_le_add (mul_le_mul_of_nonneg_left hm hc) ht
  simpa only [mul_assoc] using hh
