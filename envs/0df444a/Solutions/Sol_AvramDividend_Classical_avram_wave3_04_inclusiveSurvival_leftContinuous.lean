-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_04_inclusiveSurvival_leftContinuous
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T13:29:15.996605+00:00
-- url     : https://prove2.me/submissions/c1a926c6-535a-446f-a6a3-9dddebfaec3a

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

/-- The indicator of the inclusive interval before an extended nonnegative
clock is continuous from the left, including at the stopping clock. -/
theorem solution (τ : ℝ≥0∞) (t : ℝ≥0) :
    ContinuousWithinAt
      (fun s : ℝ≥0 => if (s : ℝ≥0∞) ≤ τ then (1 : ℝ) else 0)
      (Set.Iic t) t := by
  change Tendsto
    (fun s : ℝ≥0 => if (s : ℝ≥0∞) ≤ τ then (1 : ℝ) else 0)
    (𝓝[Set.Iic t] t)
    (𝓝 (if (t : ℝ≥0∞) ≤ τ then (1 : ℝ) else 0))
  by_cases ht : (t : ℝ≥0∞) ≤ τ
  · have heq : (fun s : ℝ≥0 =>
        if (s : ℝ≥0∞) ≤ τ then (1 : ℝ) else 0) =ᶠ[𝓝[Set.Iic t] t]
        (fun _ => (1 : ℝ)) := by
      filter_upwards [self_mem_nhdsWithin] with s hs
      simp [((ENNReal.coe_le_coe.mpr hs).trans ht)]
    simpa [ht] using (tendsto_const_nhds : Tendsto
      (fun _ : ℝ≥0 => (1 : ℝ)) (𝓝[Set.Iic t] t) (𝓝 1)).congr' heq.symm
  · have hlt : τ < (t : ℝ≥0∞) := lt_of_not_ge ht
    have hcont : Continuous (fun s : ℝ≥0 => (s : ℝ≥0∞)) := by fun_prop
    have hco : Tendsto (fun s : ℝ≥0 => (s : ℝ≥0∞))
        (𝓝[Set.Iic t] t) (𝓝 (t : ℝ≥0∞)) :=
      hcont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    have hregion : Set.Ioi τ ∈ 𝓝 (t : ℝ≥0∞) :=
      isOpen_Ioi.mem_nhds hlt
    have heq : (fun s : ℝ≥0 =>
        if (s : ℝ≥0∞) ≤ τ then (1 : ℝ) else 0) =ᶠ[𝓝[Set.Iic t] t]
        (fun _ => (0 : ℝ)) := by
      filter_upwards [hco.eventually hregion] with s hs
      simp [not_le.mpr hs]
    have hneq : ¬ (t : ℝ≥0∞) ≤ τ := ht
    simpa [hneq] using (tendsto_const_nhds : Tendsto
      (fun _ : ℝ≥0 => (0 : ℝ)) (𝓝[Set.Iic t] t) (𝓝 0)).congr' heq.symm
