-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_04_inclusiveSurvival_stronglyPredictable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T13:36:31.143995+00:00
-- url     : https://prove2.me/submissions/f095208e-aeb9-4fa9-a988-31a66a8dfe22

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_strongAdapted_leftContinuous_predictable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

private theorem wave3_04_survival_leftContinuous
    (τ : ℝ≥0∞) (t : ℝ≥0) :
    ContinuousWithinAt
      (fun s : ℝ≥0 => if (s : ℝ≥0∞) ≤ τ then (1 : ℝ) else 0)
      (Iic t) t := by
  change Tendsto
    (fun s : ℝ≥0 => if (s : ℝ≥0∞) ≤ τ then (1 : ℝ) else 0)
    (𝓝[Iic t] t)
    (𝓝 (if (t : ℝ≥0∞) ≤ τ then (1 : ℝ) else 0))
  by_cases ht : (t : ℝ≥0∞) ≤ τ
  · have heq : (fun s : ℝ≥0 =>
        if (s : ℝ≥0∞) ≤ τ then (1 : ℝ) else 0) =ᶠ[𝓝[Iic t] t]
        (fun _ => (1 : ℝ)) := by
      filter_upwards [self_mem_nhdsWithin] with s hs
      simp [((ENNReal.coe_le_coe.mpr hs).trans ht)]
    simpa [ht] using (tendsto_const_nhds : Tendsto
      (fun _ : ℝ≥0 => (1 : ℝ)) (𝓝[Iic t] t) (𝓝 1)).congr' heq.symm
  · have hlt : τ < (t : ℝ≥0∞) := lt_of_not_ge ht
    have hcont : Continuous (fun s : ℝ≥0 => (s : ℝ≥0∞)) := by fun_prop
    have hco : Tendsto (fun s : ℝ≥0 => (s : ℝ≥0∞))
        (𝓝[Iic t] t) (𝓝 (t : ℝ≥0∞)) :=
      hcont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    have hregion : Ioi τ ∈ 𝓝 (t : ℝ≥0∞) :=
      isOpen_Ioi.mem_nhds hlt
    have heq : (fun s : ℝ≥0 =>
        if (s : ℝ≥0∞) ≤ τ then (1 : ℝ) else 0) =ᶠ[𝓝[Iic t] t]
        (fun _ => (0 : ℝ)) := by
      filter_upwards [hco.eventually hregion] with s hs
      simp [not_le.mpr hs]
    have hneq : ¬ (t : ℝ≥0∞) ≤ τ := ht
    simpa [hneq] using (tendsto_const_nhds : Tendsto
      (fun _ : ℝ≥0 => (0 : ℝ)) (𝓝[Iic t] t) (𝓝 0)).congr' heq.symm

private theorem wave3_04_survival_strongAdapted
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (τ : Ω → ℝ≥0∞) (hτ : IsStoppingTime 𝓕 τ) :
    StronglyAdapted 𝓕
      (fun t ω => if (t : ℝ≥0∞) ≤ τ ω then (1 : ℝ) else 0) := by
  intro t
  have hsurvive : MeasurableSet[𝓕 t]
      {ω : Ω | (t : ℝ≥0∞) ≤ τ ω} :=
    hτ.measurableSet_ge t
  exact (Measurable.ite hsurvive measurable_const measurable_const).stronglyMeasurable

/-- The inclusive survival indicator of any stopping time is predictable
under the same (possibly unaugmented) filtration. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (τ : Ω → ℝ≥0∞) (hτ : IsStoppingTime 𝓕 τ) :
    IsStronglyPredictable 𝓕
      (fun t ω => if (t : ℝ≥0∞) ≤ τ ω then (1 : ℝ) else 0) := by
  have hA := wave3_04_survival_strongAdapted τ hτ
  have hC : ∀ ω (t : ℝ≥0),
      ContinuousWithinAt
        (fun s : ℝ≥0 =>
          if (s : ℝ≥0∞) ≤ τ ω then (1 : ℝ) else 0) (Iic t) t := by
    intro ω t
    exact wave3_04_survival_leftContinuous (τ ω) t
  exact avram_wave3_04_strongAdapted_leftContinuous_predictable hA hC
