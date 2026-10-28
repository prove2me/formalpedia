-- Prove2me | solution 1 for AvramDividend.Classical.esscher_weighted_negative_tail_real_tendsto_top_of_small_band
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T09:15:48.16736+00:00
-- url     : https://prove2.me/submissions/097b261d-3f9d-460b-a8ab-4ff72062be1c

import Theorems.Thm_AvramDividend_Classical_esscher_weighted_negative_tail_ge_small_band
import Theorems.Thm_AvramDividend_Classical_negative_jump_small_band_tendsto_top
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Data.ENNReal.Real
import Mathlib.Analysis.Complex.Exponential

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped ENNReal

/-- Infinite negative-jump intensity is retained in finite Esscher-weighted
truncated tails, by a uniform positive small-band density floor. -/
theorem solution
    (ν : Measure ℝ) (φ : ℝ) (hφ : 0 ≤ φ)
    (hfar : ν (Iic (-1 : ℝ)) < ⊤)
    (hfinite : ∀ x : ℝ, 0 < x → ν (Iio (-x)) < ⊤)
    (hweighted : ∀ x : ℝ, 0 < x →
      (ν.withDensity (fun y : ℝ => ENNReal.ofReal (Real.exp (φ * y))))
        (Iio (-x)) < ⊤)
    (htail : Tendsto (fun x : ℝ => (ν (Iio (-x))).toReal)
      (nhdsWithin (0 : ℝ) (Ioi 0)) atTop) :
    Tendsto (fun x : ℝ =>
      ((ν.withDensity (fun y : ℝ => ENNReal.ofReal (Real.exp (φ * y))))
        (Iio (-x))).toReal)
      (nhdsWithin (0 : ℝ) (Ioi 0)) atTop := by
  have hsmall :=
    negative_jump_small_band_tendsto_top ν hfar hfinite htail
  have hc : 0 < Real.exp (-φ) := Real.exp_pos _
  refine tendsto_atTop.2 ?_
  intro M
  have hev := (tendsto_atTop.1 hsmall) (M / Real.exp (-φ))
  filter_upwards [hev, self_mem_nhdsWithin] with x hx hxpos
  have hweight := esscher_weighted_negative_tail_ge_small_band
    ν φ x hφ
  have hweightReal :=
    ENNReal.toReal_mono (ne_of_lt (hweighted x hxpos)) hweight
  have hbound :
      Real.exp (-φ) * (ν (Ioo (-1 : ℝ) (-x))).toReal ≤
        ((ν.withDensity (fun y : ℝ =>
          ENNReal.ofReal (Real.exp (φ * y)))) (Iio (-x))).toReal := by
    simpa only [ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (le_of_lt hc)] using hweightReal
  have hscaled :
      M ≤ Real.exp (-φ) * (ν (Ioo (-1 : ℝ) (-x))).toReal := by
    have h := (div_le_iff₀ hc).mp hx
    simpa only [mul_comm] using h
  exact hscaled.trans hbound
