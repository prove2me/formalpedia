-- Prove2me | solution 1 for AvramDividend.Classical.bv_signed_generator_kernel_ae_measurable_negative
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T11:47:45.362342+00:00
-- url     : https://prove2.me/submissions/0a48ef1a-5fc6-4c99-b4a0-f56690c27531

import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat07_bv_signed_compensated_kernel_joint_measurable
import Theorems.Thm_AvramDividend_Classical_generatorIntegrand_negative_jump_reflection
import Theorems.Thm_AvramDividend_Classical_levy_negative_jump_measure_sFinite

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- The signed negative-jump generator kernel is jointly measurable up to null sets. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (W : ℝ → ℝ) (hWmon : Monotone W) (θ : ℝ) :
    AEStronglyMeasurable (fun p : ℝ × ℝ =>
      Real.exp (-(θ * p.1)) *
        SpectrallyNegativeLevy.generatorIntegrand W p.1 p.2)
      ((volume.restrict (Ioi (0 : ℝ))).prod
        (X.ν.restrict (Iio (0 : ℝ)))) := by
  let μ : Measure ℝ := volume.restrict (Ioi (0 : ℝ))
  let ν : Measure ℝ := X.ν.restrict (Iio (0 : ℝ))
  haveI : SFinite ν := levy_negative_jump_measure_sFinite X
  have hm : Measurable (Prod.map (id : ℝ → ℝ) (fun y : ℝ => -y)) :=
    measurable_id.prodMap measurable_neg
  have hbase : Measurable (fun p : ℝ × ℝ =>
      Real.exp (-(θ * p.1)) *
        (W (p.1 - p.2) - W p.1 +
          (if p.2 < 1 then p.2 * deriv W p.1 else 0))) :=
    chat07_bv_signed_compensated_kernel_joint_measurable W hWmon θ
  have hreflect : Measurable ((fun p : ℝ × ℝ =>
      Real.exp (-(θ * p.1)) *
        (W (p.1 - p.2) - W p.1 +
          (if p.2 < 1 then p.2 * deriv W p.1 else 0))) ∘
      Prod.map (id : ℝ → ℝ) (fun y : ℝ => -y)) :=
    hbase.comp hm
  have hν : ∀ᵐ y ∂ν, y < 0 := by
    simpa only [ν, mem_Iio] using
      (ae_restrict_mem measurableSet_Iio :
        ∀ᵐ y : ℝ ∂(X.ν.restrict (Iio (0 : ℝ))), y ∈ Iio (0 : ℝ))
  have hprod : ∀ᵐ p : ℝ × ℝ ∂μ.prod ν, p.2 < 0 := by
    apply (Measure.ae_prod_iff_ae_ae
      (measurableSet_Iio.preimage measurable_snd)).2
    filter_upwards [] with x
    exact hν
  have heq :
      ((fun p : ℝ × ℝ =>
        Real.exp (-(θ * p.1)) *
          (W (p.1 - p.2) - W p.1 +
            (if p.2 < 1 then p.2 * deriv W p.1 else 0))) ∘
        Prod.map (id : ℝ → ℝ) (fun y : ℝ => -y)) =ᵐ[μ.prod ν]
      (fun p : ℝ × ℝ =>
        Real.exp (-(θ * p.1)) *
          SpectrallyNegativeLevy.generatorIntegrand W p.1 p.2) := by
    filter_upwards [hprod] with p hp
    rcases p with ⟨x, y⟩
    simpa only [Function.comp_apply, Prod.map_apply, id_eq] using
      congrArg (fun z : ℝ => Real.exp (-(θ * x)) * z)
        (generatorIntegrand_negative_jump_reflection W x y hp)
  exact hreflect.aestronglyMeasurable.congr heq
