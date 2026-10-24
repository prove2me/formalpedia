-- Prove2me | solution 1 for AvramDividend.Classical.causal_reflected_kernel_right_interval_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T14:37:58.791+00:00
-- url     : https://prove2.me/submissions/210fbd23-9490-4c53-93ae-25db0b8ff729

import Mathlib.Analysis.Convolution

open MeasureTheory Set

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- Reflection of a causal interval preserves kernel integrability. -/
theorem solution
    (κ : ℝ → ℝ) (x u : ℝ)
    (hκ : IntervalIntegrable κ volume 0 (x - u)) :
    IntervalIntegrable (fun s : ℝ => κ (x - s)) volume u x := by
  have hrev := (hκ.comp_sub_left x).symm
  convert hrev using 1 <;> ring
