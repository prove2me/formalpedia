-- Prove2me | solution 1 for AvramDividend.Classical.esscher_weighted_negative_tail_real_tendsto_top
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T09:29:33.490995+00:00
-- url     : https://prove2.me/submissions/92fdefef-21aa-4923-9257-1d179f55a867

import Theorems.Thm_AvramDividend_Classical_esscher_weighted_negative_tail_le_unweighted
import Theorems.Thm_AvramDividend_Classical_esscher_weighted_negative_tail_real_ge_small_band
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Analysis.Complex.Exponential

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped ENNReal

/-- Positive Esscher reweighting preserves small-jump origin divergence. -/
theorem solution
    (ν : Measure ℝ) (φ : ℝ) (hφ : 0 ≤ φ)
    (hfinite : ∀ x : ℝ, 0 < x → ν (Iio (-x)) < ⊤)
    (hsmall : Tendsto
      (fun x : ℝ => (ν (Ioo (-1 : ℝ) (-x))).toReal)
      (nhdsWithin (0 : ℝ) (Ioi 0)) atTop) :
    Tendsto
      (fun x : ℝ =>
        ((ν.withDensity (fun y : ℝ => ENNReal.ofReal (Real.exp (φ * y))))
          (Iio (-x))).toReal)
      (nhdsWithin (0 : ℝ) (Ioi 0)) atTop := by
  have hc : 0 < Real.exp (-φ) := Real.exp_pos _
  have hbound : ∀ x : ℝ, 0 < x →
      Real.exp (-φ) * (ν (Ioo (-1 : ℝ) (-x))).toReal ≤
        ((ν.withDensity (fun y : ℝ => ENNReal.ofReal (Real.exp (φ * y))))
          (Iio (-x))).toReal := by
    intro x hx
    have hweightedfinite :
        (ν.withDensity (fun y : ℝ => ENNReal.ofReal (Real.exp (φ * y))))
          (Iio (-x)) < ⊤ :=
      (esscher_weighted_negative_tail_le_unweighted ν φ x hφ hx).trans_lt
        (hfinite x hx)
    exact esscher_weighted_negative_tail_real_ge_small_band ν φ x hφ hweightedfinite
  rw [Filter.tendsto_atTop] at hsmall ⊢
  intro b
  filter_upwards [hsmall (b / Real.exp (-φ)), self_mem_nhdsWithin] with x hxb hxp
  have hx : 0 < x := hxp
  have hscale : b ≤ Real.exp (-φ) * (ν (Ioo (-1 : ℝ) (-x))).toReal := by
    calc
      b ≤ (ν (Ioo (-1 : ℝ) (-x))).toReal * Real.exp (-φ) :=
        (div_le_iff₀ hc).1 hxb
      _ = Real.exp (-φ) * (ν (Ioo (-1 : ℝ) (-x))).toReal := mul_comm _ _
  exact hscale.trans (hbound x hx)
