-- Prove2me | solution 1 for AvramDividend.Classical.avram_gledger125_original_zero_clock_cash_components_vanish
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T17:09:37.338201+00:00
-- url     : https://prove2.me/submissions/a0ac006c-b5ee-4802-8ef4-be51080d1faa

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Zero stopped time has no strict or final open-strip cash in the original path. -/
theorem solution
    {Ω : Type*} (D : ℝ≥0 → Ω → ℝ) (ω : Ω)
    (σ : ℝ≥0∞) (q δ : ℝ) :
    (∫⁻ s in paymentTimes σ ∩ Iio (0 : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s)))
      ∂(dividendMeasure D ω)).toReal = 0 ∧
    (∫⁻ s in paymentTimes σ ∩ Ioo (-δ) (0 : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s)))
      ∂(dividendMeasure D ω)).toReal = 0 := by
  have hstrict : paymentTimes σ ∩ Iio (0 : ℝ) = ∅ := by
    ext s
    simp only [paymentTimes, mem_inter_iff, mem_setOf_eq,
      mem_Iio, mem_empty_iff_false, iff_false]
    exact fun h => not_lt_of_ge h.1.1 h.2
  have hstrip : paymentTimes σ ∩ Ioo (-δ) (0 : ℝ) = ∅ := by
    ext s
    simp only [paymentTimes, mem_inter_iff, mem_setOf_eq,
      mem_Ioo, mem_empty_iff_false, iff_false]
    exact fun h => not_lt_of_ge h.1.1 h.2.2
  rw [hstrict, hstrip]
  simp
