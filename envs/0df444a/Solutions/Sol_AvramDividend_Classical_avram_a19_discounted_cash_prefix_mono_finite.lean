-- Prove2me | solution 1 for AvramDividend.Classical.avram_a19_discounted_cash_prefix_mono_finite
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T06:28:22.375504+00:00
-- url     : https://prove2.me/submissions/dbe6174a-7b8b-4d46-86c9-432e2110cd6b

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- A finite original discounted Stieltjes cash integral is monotone in its strict right endpoint. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (D : ℝ≥0 → Ω → ℝ) (ω : Ω) (σ : ℝ≥0∞)
    (q s T : ℝ) (hst : s ≤ T)
    (hFin :
      (∫⁻ t in paymentTimes σ ∩ Iio T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) ≠ ⊤) :
    (∫⁻ t in paymentTimes σ ∩ Iio s,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal ≤
    (∫⁻ t in paymentTimes σ ∩ Iio T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal := by
  have hSet : paymentTimes σ ∩ Iio s ⊆ paymentTimes σ ∩ Iio T := by
    intro t ht
    exact ⟨ht.1, lt_of_lt_of_le ht.2 hst⟩
  exact ENNReal.toReal_mono hFin (lintegral_mono_set hSet)
