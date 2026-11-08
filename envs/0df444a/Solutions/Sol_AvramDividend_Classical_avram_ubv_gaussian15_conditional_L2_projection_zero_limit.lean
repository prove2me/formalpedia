-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_gaussian15_conditional_L2_projection_zero_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T16:45:53.154439+00:00
-- url     : https://prove2.me/submissions/e305ddfa-7d9c-49ab-bf21-f81546949f12

import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondexpL2

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter
open scoped ENNReal Topology
noncomputable section

/-- Conditional centring survives passage to a Gaussian terminal L² limit
within the same probability space and the same sub-filtration. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    (𝓖 : MeasurableSpace Ω) (h𝓖 : 𝓖 ≤ mΩ)
    (Q : ℕ → Lp ℝ 2 P) (L : Lp ℝ 2 P)
    (hZero : ∀ n, (condExpL2 ℝ ℝ h𝓖) (Q n) = 0)
    (hConv : Tendsto Q atTop (𝓝 L)) :
    (condExpL2 ℝ ℝ h𝓖) L = 0 := by
  let c := condExpL2 ℝ ℝ (μ := P) h𝓖
  have hc : Continuous c := c.continuous
  have hlim : Tendsto (fun n => c (Q n)) atTop (𝓝 (c L)) :=
    (hc.tendsto L).comp hConv
  have hzero : (fun n => c (Q n)) = (fun _ => 0) := by
    funext n
    exact hZero n
  rw [hzero] at hlim
  exact tendsto_nhds_unique hlim tendsto_const_nhds
