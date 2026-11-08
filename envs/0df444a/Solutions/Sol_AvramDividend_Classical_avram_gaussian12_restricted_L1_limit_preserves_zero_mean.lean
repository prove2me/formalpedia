-- Prove2me | solution 1 for AvramDividend.Classical.avram_gaussian12_restricted_L1_limit_preserves_zero_mean
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T17:57:21.009128+00:00
-- url     : https://prove2.me/submissions/b54db3cb-8ba9-4033-96ce-207b1a623e0a

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology
open scoped ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    (A : Set Ω) (hA : MeasurableSet A)
    (Q : ℕ → Ω → ℝ) (hQI : ∀ n, Integrable (Q n) P)
    (Z : Ω → ℝ) (hZI : Integrable Z P)
    (hZero : ∀ n, (∫ ω in A, Q n ω ∂P) = 0)
    (hL1 : Tendsto
      (fun n => ∫⁻ ω in A, ‖Q n ω - Z ω‖ₑ ∂P)
      atTop (nhds (0 : ℝ≥0∞))) :
    (∫ ω in A, Z ω ∂P) = 0 := by
  have hT :=
    tendsto_integral_of_L1 Z hZI.integrableOn.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun n => (hQI n).integrableOn)) hL1
  have hZeroFun :
      (fun n : ℕ => ∫ ω in A, Q n ω ∂P) =
        (fun _ : ℕ => (0 : ℝ)) := by
    funext n
    exact hZero n
  rw [hZeroFun] at hT
  have hConst : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds (0 : ℝ)) :=
    tendsto_const_nhds
  exact (tendsto_nhds_unique hConst hT).symm
