-- Prove2me | solution 1 for AvramDividend.Classical.gaussian_levy_jump_real_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T08:39:07.489673+00:00
-- url     : https://prove2.me/submissions/b8ecbb1d-7486-4a44-bed8-65c784fbcef0

import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.Tactic.FunProp
import Theorems.Thm_AvramDividend_Classical_gaussian_levy_jump_absolute_integrable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped ENNReal
open AvramDividend.Classical

/-- Bochner integrability of the canonical negative-jump Lévy exponent. -/
theorem solution (μ : Measure ℝ) (θ : ℝ) (hθ : 0 ≤ θ)
    (hlevy : (∫⁻ z in Ioi (0 : ℝ),
      ENNReal.ofReal (min 1 (z ^ 2)) ∂μ) < ⊤) :
    IntegrableOn (fun z : ℝ =>
      Real.exp (-θ * z) - 1 +
        θ * (if z ≤ 1 then z else 0))
      (Ioi (0 : ℝ)) μ := by
  let ν : Measure ℝ := μ.restrict (Ioi (0 : ℝ))
  have hm : Measurable (fun z : ℝ =>
      Real.exp (-θ * z) - 1 +
        θ * (if z ≤ 1 then z else 0)) := by
    have hs : MeasurableSet {z : ℝ | z ≤ 1} := by
      exact measurableSet_le measurable_id
        (measurable_const : Measurable (fun _ : ℝ => (1 : ℝ)))
    have hif : Measurable (fun z : ℝ =>
        if z ≤ 1 then z else 0) :=
      measurable_id.ite hs measurable_const
    have he : Measurable (fun z : ℝ =>
        Real.exp (-θ * z) - 1) := by fun_prop
    exact he.add (measurable_const.mul hif)
  have hstrong : AEStronglyMeasurable (fun z : ℝ =>
      Real.exp (-θ * z) - 1 +
        θ * (if z ≤ 1 then z else 0)) ν :=
    hm.aestronglyMeasurable
  have habsstrong : AEStronglyMeasurable (fun z : ℝ =>
      |Real.exp (-θ * z) - 1 +
        θ * (if z ≤ 1 then z else 0)|) ν :=
    hm.abs.aestronglyMeasurable
  have habsnonneg : ∀ᵐ z : ℝ ∂ν,
      0 ≤ |Real.exp (-θ * z) - 1 +
        θ * (if z ≤ 1 then z else 0)| :=
    Filter.Eventually.of_forall (fun z => abs_nonneg _)
  have hfin :=
    gaussian_levy_jump_absolute_integrable μ θ hθ hlevy
  change (∫⁻ z : ℝ, ENNReal.ofReal
    |Real.exp (-θ * z) - 1 +
      θ * (if z ≤ 1 then z else 0)| ∂ν) < ⊤ at hfin
  have habsint : Integrable (fun z : ℝ =>
      |Real.exp (-θ * z) - 1 +
        θ * (if z ≤ 1 then z else 0)|) ν :=
    (lintegral_ofReal_ne_top_iff_integrable habsstrong habsnonneg).mp
      (ne_of_lt hfin)
  have hnormint : Integrable (fun z : ℝ =>
      ‖Real.exp (-θ * z) - 1 +
        θ * (if z ≤ 1 then z else 0)‖) ν := by
    simpa only [Real.norm_eq_abs] using habsint
  change Integrable (fun z : ℝ =>
    Real.exp (-θ * z) - 1 +
      θ * (if z ≤ 1 then z else 0)) ν
  exact (integrable_norm_iff hstrong).mp hnormint
