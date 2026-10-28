-- Prove2me | solution 1 for AvramDividend.Classical.esscher_joint_clock_event_fibrewise_disintegration
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T17:19:45.672115+00:00
-- url     : https://prove2.me/submissions/6d581e77-9549-45f5-adff-bc3bc458f40c

import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped ENNReal

/-- Disintegrate a measurable clock-dependent event under a genuine
    fibrewise tilted product measure. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [SFinite P]
    (η : Measure ℝ) [SFinite η]
    (D : Ω × ℝ → ℝ≥0∞) (hD : Measurable D)
    (A : Set (Ω × ℝ)) (hA : MeasurableSet A) :
    ((P.prod η).withDensity D) A =
      (∫⁻ t : ℝ, (P.withDensity (fun ω : Ω => D (ω, t)))
        {ω : Ω | (ω, t) ∈ A} ∂η) := by
  rw [withDensity_apply D hA]
  rw [← lintegral_indicator hA]
  rw [lintegral_prod_symm _ (hD.indicator hA).aemeasurable]
  congr 1
  funext t
  have hSlice : MeasurableSet {ω : Ω | (ω, t) ∈ A} :=
    hA.preimage (measurable_id.prodMk measurable_const)
  rw [withDensity_apply (fun ω : Ω => D (ω, t)) hSlice]
  rw [← lintegral_indicator hSlice]
  rfl
