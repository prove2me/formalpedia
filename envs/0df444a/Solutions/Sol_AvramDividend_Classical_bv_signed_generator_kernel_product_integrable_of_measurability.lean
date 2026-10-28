-- Prove2me | solution 1 for AvramDividend.Classical.bv_signed_generator_kernel_product_integrable_of_measurability
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T11:49:42.19502+00:00
-- url     : https://prove2.me/submissions/a941c480-47d9-4a6d-85ff-fd3066c01a4c

import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.Analysis.Normed.Group.Real
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat07_bv_actual_levy_compensated_kernel_product_integrable
import Theorems.Thm_AvramDividend_Classical_integrable_product_signed_jump_of_neg_map
import Theorems.Thm_AvramDividend_Classical_generatorIntegrand_negative_jump_reflection
import Theorems.Thm_AvramDividend_Classical_levy_negative_jump_measure_sFinite

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Transfer BV jump-kernel product integrability from magnitudes to negative jumps. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hbv : X.BoundedVariation)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hWmon : Monotone W)
    (θ : ℝ) (hθ : 0 ≤ θ) (hqθ : q < X.ψ θ)
    (hAEm : AEStronglyMeasurable (fun p : ℝ × ℝ =>
      Real.exp (-(θ * p.1)) *
        SpectrallyNegativeLevy.generatorIntegrand W p.1 p.2)
      ((volume.restrict (Ioi (0 : ℝ))).prod
        (X.ν.restrict (Iio (0 : ℝ))))) :
    Integrable (fun p : ℝ × ℝ =>
      Real.exp (-(θ * p.1)) *
        SpectrallyNegativeLevy.generatorIntegrand W p.1 p.2)
      ((volume.restrict (Ioi (0 : ℝ))).prod
        (X.ν.restrict (Iio (0 : ℝ)))) := by
  let μ : Measure ℝ := volume.restrict (Ioi (0 : ℝ))
  let ν : Measure ℝ := X.ν.restrict (Iio (0 : ℝ))
  haveI : SFinite ν := levy_negative_jump_measure_sFinite X
  have hpos := chat07_bv_actual_levy_compensated_kernel_product_integrable
    X hbv q W hW hWmon θ hθ hqθ
  have hν : ∀ᵐ y ∂ν, y < 0 := by
    simpa only [ν, mem_Iio] using
      (ae_restrict_mem measurableSet_Iio :
        ∀ᵐ y : ℝ ∂(X.ν.restrict (Iio (0 : ℝ))),
          y ∈ Iio (0 : ℝ))
  have hprod : ∀ᵐ p : ℝ × ℝ ∂μ.prod ν, p.2 < 0 := by
    apply (Measure.ae_prod_iff_ae_ae
      (measurableSet_Iio.preimage measurable_snd)).2
    filter_upwards [] with x
    exact hν
  have hFG :
      ((fun p : ℝ × ℝ =>
          Real.exp (-(θ * p.1)) *
            |W (p.1 - p.2) - W p.1 +
              (if p.2 < 1 then p.2 * deriv W p.1 else 0)|) ∘
        Prod.map (id : ℝ → ℝ) (fun y : ℝ => -y)) =ᵐ[μ.prod ν]
      (fun p : ℝ × ℝ =>
        Real.exp (-(θ * p.1)) *
          |SpectrallyNegativeLevy.generatorIntegrand W p.1 p.2|) := by
    filter_upwards [hprod] with p hp
    rcases p with ⟨x, y⟩
    simpa only [Function.comp_apply, Prod.map_apply, id_eq] using
      congrArg (fun z : ℝ => Real.exp (-(θ * x)) * |z|)
        (generatorIntegrand_negative_jump_reflection W x y hp)
  have hAbs : Integrable (fun p : ℝ × ℝ =>
      Real.exp (-(θ * p.1)) *
        |SpectrallyNegativeLevy.generatorIntegrand W p.1 p.2|)
      (μ.prod ν) :=
    integrable_product_signed_jump_of_neg_map μ ν _ _ hpos hFG
  have hNorm : Integrable (fun p : ℝ × ℝ =>
      ‖Real.exp (-(θ * p.1)) *
        SpectrallyNegativeLevy.generatorIntegrand W p.1 p.2‖)
      (μ.prod ν) := by
    convert hAbs using 1
    funext p
    simp only [Real.norm_eq_abs, abs_mul,
      abs_of_pos (Real.exp_pos _)]
  exact (integrable_norm_iff hAEm).1 hNorm
