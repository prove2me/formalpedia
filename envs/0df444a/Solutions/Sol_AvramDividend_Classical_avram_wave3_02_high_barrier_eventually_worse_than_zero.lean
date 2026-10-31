-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_02_high_barrier_eventually_worse_than_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T20:48:01.738538+00:00
-- url     : https://prove2.me/submissions/ef5c3045-8ed5-476f-a665-97d89e4d1ca7

import Mathlib.Data.ENNReal.Real
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.OrderClosed
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_avram_wave3_02_positive_reserve_high_barrier_value_zero
import Theorems.Thm_AvramDividend_Classical_avram_wave3_02_all_nonnegative_barriers_sup

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

/-- For every positive reserve, all sufficiently high payout thresholds
yield strictly less expected discounted dividends than the genuine zero cap. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (x : ℝ) (hx : 0 < x) :
    ∀ᶠ a : ℝ in atTop,
      dividendValue X q x (barrierStrategy X x a) <
        dividendValue X q x (barrierStrategy X x 0) := by
  have hlim :=
    avram_wave3_02_positive_reserve_high_barrier_value_zero
      X hX q hq W hW x hx
  have hevent : ∀ᶠ a : ℝ in atTop,
      dividendValue X q x (barrierStrategy X x a) < ENNReal.ofReal x :=
    Filter.Tendsto.eventually_lt_const (ENNReal.ofReal_pos.mpr hx) hlim
  have heq : dividendValue X q x (barrierStrategy X x 0) =
      ENNReal.ofReal x + barrierSupValue X 0 q := by
    simpa using
      (avram_wave3_02_all_nonnegative_barriers_sup X hX q hq W hW
        0 (le_refl (0 : ℝ)) x (le_of_lt hx))
  have hzero : ENNReal.ofReal x ≤
      dividendValue X q x (barrierStrategy X x 0) := by
    rw [heq]
    exact le_add_of_nonneg_right (zero_le : (0 : ENNReal) ≤ barrierSupValue X 0 q)
  filter_upwards [hevent] with a ha
  exact lt_of_lt_of_le ha hzero
