-- Prove2me | solution 1 for AvramDividend.Classical.avram_sweep16_20261106_strict_clipped_cash_le_natural_closed
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T06:42:19.291728+00:00
-- url     : https://prove2.me/submissions/06135481-48d9-41d6-8d0e-346b31731f59

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_sweep16_20261106_strict_clipped_times_subset_natural_closed
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (σ : Ω → ℝ≥0∞) (μ : Ω → Measure ℝ) (f : Ω → ℝ → ℝ≥0∞)
    (n : ℕ) (T : ℝ) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (min (σ ω) (n : ℝ≥0∞)) ∩ Iic T,
      f ω t ∂(μ ω) ∂P) ≤
    (∫⁻ ω, ∫⁻ t in paymentTimes (σ ω) ∩
      Iic (((min (σ ω) (n : ℝ≥0∞)).toNNReal : ℝ)),
      f ω t ∂(μ ω) ∂P) := by
  apply lintegral_mono
  intro ω
  apply lintegral_mono_set
  intro t ht
  exact avram_sweep16_20261106_strict_clipped_times_subset_natural_closed (σ ω) n ht.1
