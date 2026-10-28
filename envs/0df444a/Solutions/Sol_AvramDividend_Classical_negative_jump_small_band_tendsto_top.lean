-- Prove2me | solution 1 for AvramDividend.Classical.negative_jump_small_band_tendsto_top
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T09:02:04.849308+00:00
-- url     : https://prove2.me/submissions/0c5c6d85-f2bc-4543-b433-4b10e405b48e

import Theorems.Thm_AvramDividend_Classical_negative_jump_real_tail_tendsto_top
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic.Linarith

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped ENNReal

/-- A fixed finite far-jump mass cannot account for the diverging negative tail. -/
theorem solution
    (ν : Measure ℝ)
    (hfar : ν (Iic (-1 : ℝ)) < ⊤)
    (hfinite : ∀ x : ℝ, 0 < x → ν (Iio (-x)) < ⊤)
    (htail : Tendsto (fun x : ℝ => (ν (Iio (-x))).toReal)
      (nhdsWithin (0 : ℝ) (Ioi 0)) atTop) :
    Tendsto (fun x : ℝ => (ν (Ioo (-1 : ℝ) (-x))).toReal)
      (nhdsWithin (0 : ℝ) (Ioi 0)) atTop := by
  have hnear : ∀ᶠ x : ℝ in nhdsWithin (0 : ℝ) (Ioi 0), x < 1 :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds
      (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))
  rw [Filter.tendsto_atTop] at htail ⊢
  intro b
  filter_upwards [htail (b + (ν (Iic (-1 : ℝ))).toReal), hnear,
    self_mem_nhdsWithin] with x hlarge hx1 hxpos
  have hx : 0 < x := hxpos
  have hsets : Iio (-x) = Iic (-1 : ℝ) ∪ Ioo (-1) (-x) := by
    ext y
    simp only [mem_Iio, mem_union, mem_Iic, mem_Ioo]
    constructor
    · intro hy
      by_cases hle : y ≤ -1
      · exact Or.inl hle
      · exact Or.inr ⟨lt_of_not_ge hle, hy⟩
    · intro hy
      rcases hy with hy | hy
      · linarith
      · exact hy.2
  have hdisj : Disjoint (Iic (-1 : ℝ)) (Ioo (-1) (-x)) := by
    apply Set.disjoint_left.mpr
    intro y hy1 hy2
    exact (not_lt_of_ge hy1) hy2.1
  have hbandfinite : ν (Ioo (-1 : ℝ) (-x)) ≠ ⊤ := by
    have hsubset : Ioo (-1 : ℝ) (-x) ⊆ Iio (-x) :=
      fun y hy => hy.2
    exact ne_of_lt ((measure_mono hsubset).trans_lt (hfinite x hx))
  have hsplit : (ν (Iio (-x))).toReal =
      (ν (Iic (-1 : ℝ))).toReal + (ν (Ioo (-1) (-x))).toReal := by
    rw [hsets, measure_union hdisj measurableSet_Ioo,
      ENNReal.toReal_add (ne_of_lt hfar) hbandfinite]
  linarith
