-- Prove2me | solution 1 for AvramDividend.Classical.avram_bva46_original_strict_cash_prefix_pointwise_monotone
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T01:22:33.250678+00:00
-- url     : https://prove2.me/submissions/b48b1798-7a0c-4db6-a0b1-6e1ac1930f56

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_literal_stopped_payment_cash_lintegral_finite
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 ≤ q) (T : ℝ) (hT : 0 < T)
    (δ : ℝ) (hδ : 0 ≤ δ) (ω : Ω) :
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (T - δ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal ≤
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal := by
  let S : ℝ≥0 := ⟨T, le_of_lt hT⟩
  have hFinClosed :
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) < ⊤ := by
    simpa only [show (S : ℝ) = T from rfl] using
      (avram_p4_d_dividend_original_literal_stopped_payment_cash_lintegral_finite
        D hD.1.1 ω (ruinTime X x D ω) S q hq)
  have hFinStrict :
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) ≠ ⊤ := by
    apply ne_of_lt
    exact lt_of_le_of_lt (lintegral_mono_set
      (show paymentTimes (ruinTime X x D ω) ∩ Iio T ⊆
        paymentTimes (ruinTime X x D ω) ∩ Iic T from
          inter_subset_inter_right _ Iio_subset_Iic_self)) hFinClosed
  apply ENNReal.toReal_mono hFinStrict
  exact lintegral_mono_set
    (inter_subset_inter_right _ (Iio_subset_Iio (sub_le_self T hδ)))
