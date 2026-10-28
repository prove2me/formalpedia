-- Prove2me | solution 1 for AvramDividend.Classical.esscher_kernel_diverges_of_negative_tail_lower
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T08:36:46.046498+00:00
-- url     : https://prove2.me/submissions/f586f17e-249d-4091-856d-428d23741040

import Theorems.Thm_AvramDividend_Classical_negative_jump_real_tail_tendsto_top
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Data.ENNReal.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Filter Set
open scoped ENNReal Topology

/-- Positive scaling and the atTop comparison criterion transfer Lévy-tail divergence. -/
theorem solution
    (ν : Measure ℝ)
    (hνint : ∫⁻ y, ENNReal.ofReal (min 1 (y ^ 2)) ∂ν < ⊤)
    (hνinf : ν (Iio (0 : ℝ)) = ⊤)
    (k : ℝ → ℝ) (c : ℝ) (hc : 0 < c)
    (hk : ∀ x : ℝ, 0 < x → c * (ν (Iio (-x))).toReal ≤ k x) :
    Tendsto k (nhdsWithin (0 : ℝ) (Ioi 0)) atTop := by
  have htail := negative_jump_real_tail_tendsto_top ν hνint hνinf
  rw [Filter.tendsto_atTop] at htail ⊢
  intro b
  filter_upwards [htail (b / c), self_mem_nhdsWithin] with x hx hpos
  have hxpos : 0 < x := hpos
  have hmul := mul_le_mul_of_nonneg_left hx hc.le
  have hcancel : c * (b / c) = b := by
    field_simp [ne_of_gt hc]
  have hlower : b ≤ c * (ν (Iio (-x))).toReal := by
    simpa only [hcancel] using hmul
  exact hlower.trans (hk x hxpos)
