-- Prove2me | solution 1 for AvramDividend.Classical.simple_reserve_approxOn_real_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T12:22:13.83966+00:00
-- url     : https://prove2.me/submissions/024cc099-3df9-4078-974c-7921e90c192e

import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Theorems.Thm_AvramDividend_Classical_real_L1_integral_tendsto_zero_of_enorm

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter MeasureTheory Set
open scoped ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (Z : Ω → ℝ)
    (hZ : Measurable Z) (hI : Integrable Z P) :
    Tendsto
      (fun n : ℕ =>
        ∫ ω, |(SimpleFunc.approxOn Z hZ (Set.range Z ∪ {0}) 0
          (by simp) n) ω - Z ω| ∂P)
      atTop (nhds 0) := by
  let A (n : ℕ) : Ω → ℝ :=
    SimpleFunc.approxOn Z hZ (Set.range Z ∪ {0}) 0 (by simp) n
  have hInt (n : ℕ) :
      Integrable (fun ω => A n ω - Z ω) P := by
    exact (SimpleFunc.integrable_approxOn_range hZ hI n).sub hI
  have hApprox :
      Tendsto (fun n : ℕ =>
        ∫⁻ ω, ‖A n ω - Z ω‖ₑ ∂P) atTop (nhds 0) := by
    exact SimpleFunc.tendsto_approxOn_range_L1_enorm hZ hI
  exact AvramDividend.Classical.real_L1_integral_tendsto_zero_of_enorm
    P (fun n ω => A n ω - Z ω) hInt hApprox
