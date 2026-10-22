-- Prove2me | solution 1 for AvramDividend.Classical.gaussian_esscher_drift_real_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T08:28:43.756978+00:00
-- url     : https://prove2.me/submissions/62b4a35e-05c8-40ec-9427-61679b19d6c0

import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.Tactic.FunProp
import Theorems.Thm_AvramDividend_Classical_gaussian_esscher_drift_correction_integrable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped ENNReal
open AvramDividend.Classical

/-- Real integrability of the Esscher drift correction for canonical truncation. -/
theorem solution (μ : Measure ℝ) (φ : ℝ) (hφ : 0 < φ)
    (hlevy : (∫⁻ z in Ioi (0 : ℝ),
      ENNReal.ofReal (min 1 (z ^ 2)) ∂μ) < ⊤) :
    IntegrableOn (fun z : ℝ =>
      (if z ≤ 1 then z else 0) - z * Real.exp (-φ * z))
      (Ioi (0 : ℝ)) μ := by
  let ν : Measure ℝ := μ.restrict (Ioi (0 : ℝ))
  have hmeas : Measurable (fun z : ℝ =>
      (if z ≤ 1 then z else 0) - z * Real.exp (-φ * z)) := by
    have hs : MeasurableSet {z : ℝ | z ≤ 1} := by
      exact measurableSet_le measurable_id
        (measurable_const : Measurable (fun _ : ℝ => (1 : ℝ)))
    have hif : Measurable (fun z : ℝ =>
        if z ≤ 1 then z else 0) :=
      measurable_id.ite hs measurable_const
    have hm : Measurable (fun z : ℝ =>
        z * Real.exp (-φ * z)) := by
      fun_prop
    exact hif.sub hm
  have hstrong : AEStronglyMeasurable (fun z : ℝ =>
      (if z ≤ 1 then z else 0) - z * Real.exp (-φ * z)) ν :=
    hmeas.aestronglyMeasurable
  have habsstrong : AEStronglyMeasurable (fun z : ℝ =>
      |(if z ≤ 1 then z else 0) - z * Real.exp (-φ * z)|) ν :=
    hmeas.abs.aestronglyMeasurable
  have habsnonneg : ∀ᵐ z : ℝ ∂ν,
      0 ≤ |(if z ≤ 1 then z else 0) - z * Real.exp (-φ * z)| :=
    Filter.Eventually.of_forall (fun z => abs_nonneg _)
  have hfin :=
    gaussian_esscher_drift_correction_integrable μ φ hφ hlevy
  change (∫⁻ z : ℝ, ENNReal.ofReal
    |(if z ≤ 1 then z else 0) - z * Real.exp (-φ * z)| ∂ν) < ⊤ at hfin
  have habsint : Integrable (fun z : ℝ =>
      |(if z ≤ 1 then z else 0) - z * Real.exp (-φ * z)|) ν :=
    (lintegral_ofReal_ne_top_iff_integrable habsstrong habsnonneg).mp
      (ne_of_lt hfin)
  have hnormint : Integrable (fun z : ℝ =>
      ‖(if z ≤ 1 then z else 0) - z * Real.exp (-φ * z)‖) ν := by
    simpa only [Real.norm_eq_abs] using habsint
  change Integrable (fun z : ℝ =>
    (if z ≤ 1 then z else 0) - z * Real.exp (-φ * z)) ν
  exact (integrable_norm_iff hstrong).mp hnormint
