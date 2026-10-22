-- Prove2me | solution 1 for AvramDividend.Classical.simple_reserve_approxOn_weighted_real_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T18:12:51.497714+00:00
-- url     : https://prove2.me/submissions/761b462a-3f84-4874-8fee-8c7677a44a82

import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Theorems.Thm_AvramDividend_Classical_simple_reserve_approxOn_real_L1

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter MeasureTheory Set

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (Z : Ω → ℝ)
    (hZ : Measurable Z) (hI : Integrable Z P) (L : ℝ) :
    Tendsto (fun n : ℕ =>
      ∫ ω, L * |(SimpleFunc.approxOn Z hZ
          (Set.range Z ∪ {0}) 0 (by simp) n) ω - Z ω| ∂P)
      atTop (nhds 0) := by
  have h := AvramDividend.Classical.simple_reserve_approxOn_real_L1
    P Z hZ hI
  simpa only [integral_const_mul, mul_zero] using h.const_mul L
