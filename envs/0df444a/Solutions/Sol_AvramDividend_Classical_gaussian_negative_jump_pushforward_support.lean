-- Prove2me | solution 1 for AvramDividend.Classical.gaussian_negative_jump_pushforward_support
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T12:31:28.053256+00:00
-- url     : https://prove2.me/submissions/db478fb3-8239-432c-a6f0-c5dd2b137f51

import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set

/-- Negating a spectrally negative jump measure yields a measure
supported on strictly positive jump magnitudes. -/
theorem solution (ν : Measure ℝ)
    (hν : ν (Ici (0 : ℝ)) = 0) :
    (ν.map (fun y : ℝ => -y)) (Iic (0 : ℝ)) = 0 := by
  let n : ℝ → ℝ := fun y => -y
  have hn : Measurable n := measurable_id.neg
  have hpre : n ⁻¹' Iic (0 : ℝ) = Ici (0 : ℝ) := by
    ext y
    simp only [mem_preimage, mem_Iic, mem_Ici, n]
    constructor
    · intro h
      linarith
    · intro h
      linarith
  change (ν.map n) (Iic (0 : ℝ)) = 0
  rw [Measure.map_apply hn measurableSet_Iic, hpre]
  exact hν
