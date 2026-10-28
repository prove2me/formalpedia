-- Prove2me | solution 1 for AvramDividend.Classical.causal_damped_positive_L1_intervalIntegrable
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T18:12:12.122723+00:00
-- url     : https://prove2.me/submissions/f796d610-f10f-4e4c-b25f-a0198124b519

import Mathlib
open MeasureTheory Set
theorem solution
    (P : ℝ → ℝ) (w x : ℝ)
    (hP : IntegrableOn P (Ioi (0 : ℝ)) volume)
    (hx : 0 < x) :
    IntervalIntegrable
      (fun s : ℝ => Real.exp (-w * (x - s)) * P s)
      volume 0 x := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hx.le]
  have hP' : IntegrableOn P (Icc 0 x) volume := by
    rw [integrableOn_Icc_iff_integrableOn_Ioc]
    exact hP.mono_set Ioc_subset_Ioi_self
  have hc : ContinuousOn (fun s : ℝ => Real.exp (-w * (x - s))) (Icc 0 x) := by fun_prop
  exact hP'.continuousOn_mul hc isCompact_Icc
