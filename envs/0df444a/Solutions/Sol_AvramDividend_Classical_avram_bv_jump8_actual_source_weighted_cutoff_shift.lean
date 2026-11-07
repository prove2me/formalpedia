-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_jump8_actual_source_weighted_cutoff_shift
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T18:46:56.928002+00:00
-- url     : https://prove2.me/submissions/d65813b3-6023-4919-92f2-ebc662356a61

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bv_jump8_weighted_mark_lintegral_of_rectangle_equality
import Theorems.Thm_AvramDividend_Classical_avram_bv_jump8_actual_source_marked_rectangle_shift
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (n k : ℕ) :
    ((∫⁻ p : ℝ≥0 × ℝ,
      if 0 < p.1 ∧ p.1 ≤ (1 : ℝ≥0) ∧
        p.2 < -(1 / ((k : ℝ) + 1)) then ENNReal.ofReal (-p.2) else 0 ∂
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧
          (X.X ((n : ℝ≥0) + u) ω - X.X (n : ℝ≥0) ω) -
            Function.leftLim
              (fun v : ℝ≥0 => X.X ((n : ℝ≥0) + v) ω - X.X (n : ℝ≥0) ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          (X.X ((n : ℝ≥0) + u) ω - X.X (n : ℝ≥0) ω) -
            Function.leftLim
              (fun v : ℝ≥0 => X.X ((n : ℝ≥0) + v) ω - X.X (n : ℝ≥0) ω) u))))).toReal =
    ((∫⁻ p : ℝ≥0 × ℝ,
      if (n : ℝ≥0) < p.1 ∧ p.1 ≤ ((n + 1) : ℝ≥0) ∧
        p.2 < -(1 / ((k : ℝ) + 1)) then ENNReal.ofReal (-p.2) else 0 ∂
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))))).toReal := by
  let μ : Measure (ℝ≥0 × ℝ) :=
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧
        (X.X ((n : ℝ≥0) + u) ω - X.X (n : ℝ≥0) ω) -
          Function.leftLim
            (fun v : ℝ≥0 => X.X ((n : ℝ≥0) + v) ω - X.X (n : ℝ≥0) ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        (X.X ((n : ℝ≥0) + u) ω - X.X (n : ℝ≥0) ω) -
          Function.leftLim
            (fun v : ℝ≥0 => X.X ((n : ℝ≥0) + v) ω - X.X (n : ℝ≥0) ω) u)))
  let ν : Measure (ℝ≥0 × ℝ) :=
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
  let g : ℝ → ℝ≥0∞ :=
    fun y => if y < -(1 / ((k : ℝ) + 1)) then ENNReal.ofReal (-y) else 0
  have hg : Measurable g := by
    dsimp [g]
    have hs : MeasurableSet {y : ℝ | y < -(1 / ((k : ℝ) + 1))} :=
      measurableSet_lt measurable_id measurable_const
    have hv : Measurable (fun y : ℝ => ENNReal.ofReal (-y)) := by fun_prop
    exact hv.ite hs measurable_const
  have hRect : ∀ B : Set ℝ, MeasurableSet B →
      μ (Ioc 0 1 ×ˢ B) = ν (Ioc (n : ℝ≥0) ((n : ℝ≥0) + 1) ×ˢ B) := by
    intro B hB
    exact avram_bv_jump8_actual_source_marked_rectangle_shift X ω n B hB
  have h := avram_bv_jump8_weighted_mark_lintegral_of_rectangle_equality
    μ ν (n : ℝ≥0) 1 g hg hRect
  simpa only [μ, ν, g, ite_and, Nat.cast_add, Nat.cast_one]
    using congrArg ENNReal.toReal h
