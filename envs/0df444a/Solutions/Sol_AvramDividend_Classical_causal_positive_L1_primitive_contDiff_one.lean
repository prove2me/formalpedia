-- Prove2me | solution 1 for AvramDividend.Classical.causal_positive_L1_primitive_contDiff_one
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T11:02:21.066569+00:00
-- url     : https://prove2.me/submissions/299cdef0-ad62-4a86-8d9c-8c50615f449e

import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Theorems.Thm_AvramDividend_Classical_causal_positive_kernel_primitive_contDiff_one
import Theorems.Thm_AvramDividend_Classical_causal_positive_L1_intervalIntegrable
import Mathlib.Analysis.Calculus.ContDiff.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set

/-- Global L1 and positive-time continuity yield a C1 causal kernel primitive. -/
theorem solution
    (K : ℝ → ℝ)
    (hK : IntegrableOn K (Ioi (0 : ℝ)) volume)
    (hcont : ContinuousOn K (Ioi (0 : ℝ))) :
    ContDiffOn ℝ 1 (fun x : ℝ => ∫ s in (0 : ℝ)..x, K s) (Ioi 0) := by
  exact AvramDividend.Classical.causal_positive_kernel_primitive_contDiff_one
    K hcont (fun x hx =>
      AvramDividend.Classical.causal_positive_L1_intervalIntegrable K hK x hx)
