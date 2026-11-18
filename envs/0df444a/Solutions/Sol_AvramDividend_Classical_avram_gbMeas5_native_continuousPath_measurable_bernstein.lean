-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbMeas5_native_continuousPath_measurable_bernstein
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T19:12:46.6622+00:00
-- url     : https://prove2.me/submissions/a185b08d-fda9-4681-9445-41fb06e51f93

import Mathlib
import Definitions.Def_GlynnSTS_Limit_Setting
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set
open scoped unitInterval Topology
noncomputable section
/-- Continuous-path measurability from evaluations by uniform Bernstein approximation. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (B : Ω → C(unitInterval, ℝ))
    (hcoord : ∀ t : unitInterval,
      Measurable (fun ω : Ω => B ω t)) :
    Measurable B := by
  have hApprox (n : ℕ) :
      Measurable (fun ω : Ω => bernsteinApproximation n (B ω)) := by
    change Measurable (fun ω : Ω =>
      ∑ k : Fin (n + 1),
        bernstein n k • ContinuousMap.const unitInterval
          (B ω (bernstein.z k)))
    apply Finset.measurable_sum
    intro k hk
    have hConst :
        Measurable (fun ω : Ω =>
          ContinuousMap.const unitInterval (B ω (bernstein.z k))) :=
      (ContinuousLinearMap.const ℝ unitInterval :
        ℝ →L[ℝ] C(unitInterval, ℝ)).continuous.measurable.comp
          (hcoord (bernstein.z k))
    have hMul :
        Measurable (fun ω : Ω =>
          (bernstein n k) *
            ContinuousMap.const unitInterval (B ω (bernstein.z k))) :=
      (continuous_const.mul continuous_id).measurable.comp hConst
    simpa only [smul_eq_mul] using hMul
  have hLim : Tendsto
      (fun n : ℕ => fun ω : Ω => bernsteinApproximation n (B ω))
      atTop (𝓝 B) :=
    tendsto_pi_nhds.mpr fun ω => bernsteinApproximation_uniform (B ω)
  exact measurable_of_tendsto_metrizable hApprox hLim
