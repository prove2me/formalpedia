-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_b_rate_weighted_exponential_image_no_nonpositive_mass
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T21:08:50.539925+00:00
-- url     : https://prove2.me/submissions/7495710e-09b0-4445-91ed-7c1f253213a8

import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped ENNReal

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Y : Ω → ℝ) (hY : Measurable Y) (θ : ℝ) :
    ((μ.withDensity (fun ω =>
      ENNReal.ofReal ((Real.exp (θ * Y ω) - 1) ^ 4))).map
      (fun ω => Real.exp (θ * Y ω))) (Iic (0 : ℝ)) = 0 := by
  have hz : Measurable (fun ω => Real.exp (θ * Y ω)) :=
    (Real.measurable_exp).comp (measurable_const.mul hY)
  have hmeas : MeasurableSet (Iic (0 : ℝ)) := measurableSet_Iic
  have hpre : (fun ω => Real.exp (θ * Y ω)) ⁻¹' (Iic (0 : ℝ)) =
      (∅ : Set Ω) := by
    ext ω
    simp only [mem_preimage, mem_Iic, mem_empty_iff_false, iff_false]
    exact not_le.mpr (Real.exp_pos _)
  rw [Measure.map_apply hz hmeas, hpre]
  exact measure_empty
