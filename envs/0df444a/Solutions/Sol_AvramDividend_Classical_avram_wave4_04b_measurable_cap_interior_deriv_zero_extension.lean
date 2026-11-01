-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_04b_measurable_cap_interior_deriv_zero_extension
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T17:47:01.61447+00:00
-- url     : https://prove2.me/submissions/5dfd58ed-0011-43cc-a429-2738a90895a9

import Mathlib
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_measurable_interior_deriv_zero_extension

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section
theorem solution
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) :
    Measurable (fun y : ℝ =>
      if 0 < y ∧ ENNReal.ofReal y < C then deriv w y else 0) := by
  have hOpen : IsOpen {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} := by
    change IsOpen (Ioi (0 : ℝ) ∩ ENNReal.ofReal ⁻¹' Iio C)
    exact isOpen_Ioi.inter (isOpen_Iio.preimage ENNReal.continuous_ofReal)
  simpa only [Set.mem_setOf_eq] using
    (avram_wave4_04b_measurable_interior_deriv_zero_extension
      w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} hOpen hw)
