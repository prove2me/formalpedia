-- Prove2me | solution 1 for AvramDividend.Classical.continuous_ramp_mul_of_continuousOn_positive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T21:31:30.65056+00:00
-- url     : https://prove2.me/submissions/e1e5e2dd-c520-4223-9804-7eb12ee219a7

import Mathlib.Topology.ContinuousOn
import Theorems.Thm_AvramDividend_Classical_positive_ramp_cutoff_continuous_and_support
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical Set Filter

/-- A clipped ramp turns a positive-time continuous kernel into a continuous real function. -/
theorem solution
    (ε : ℝ) (hε : 0 < ε) (f : ℝ → ℝ)
    (hf : ContinuousOn f (Ioi (0 : ℝ))) :
    Continuous (fun x : ℝ => max (0 : ℝ) (min 1 ((x - ε) / ε)) * f x) := by
  obtain ⟨hχ, hχzero, _⟩ := positive_ramp_cutoff_continuous_and_support ε hε
  refine continuous_iff_continuousAt.mpr fun x => ?_
  by_cases hx : 0 < x
  · exact hχ.continuousAt.mul (hf.continuousAt (isOpen_Ioi.mem_nhds hx))
  · have hlt : x < ε := lt_of_le_of_lt (le_of_not_gt hx) hε
    apply (continuousAt_const : ContinuousAt (fun _ : ℝ => (0 : ℝ)) x).congr_of_eventuallyEq
    filter_upwards [isOpen_Iio.mem_nhds hlt] with y hy
    simp [hχzero y hy.le]
