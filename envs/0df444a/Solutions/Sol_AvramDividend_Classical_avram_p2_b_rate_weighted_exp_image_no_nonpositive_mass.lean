-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_b_rate_weighted_exp_image_no_nonpositive_mass
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T12:42:53.012904+00:00
-- url     : https://prove2.me/submissions/58708239-8217-432b-9606-62d14a42331e

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped ENNReal

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Y : Ω → ℝ) (hY : Measurable Y)
    (w : Ω → ℝ≥0∞) :
    ((μ.withDensity w).map (fun ω => Real.exp (Y ω))) (Iic (0 : ℝ)) = 0 := by
  have hmap : Measurable (fun ω => Real.exp (Y ω)) :=
    Real.measurable_exp.comp hY
  rw [Measure.map_apply hmap measurableSet_Iic]
  have hpre :
      (fun ω => Real.exp (Y ω)) ⁻¹' Iic (0 : ℝ) = (∅ : Set Ω) := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_empty_iff_false, iff_false]
    exact not_le_of_gt (Real.exp_pos (Y ω))
  simp [hpre]
