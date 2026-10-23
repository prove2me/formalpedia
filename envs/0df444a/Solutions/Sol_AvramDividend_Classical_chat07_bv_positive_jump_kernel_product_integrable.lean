-- Prove2me | solution 1 for AvramDividend.Classical.chat07_bv_positive_jump_kernel_product_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T08:01:54.425444+00:00
-- url     : https://prove2.me/submissions/8d9533a2-e40b-418b-a9a1-7154e9cb5123

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat07_product_integrable_of_section_norm_majorant
import Theorems.Thm_AvramDividend_Classical_chat07_bv_compensated_kernel_joint_measurable
import Theorems.Thm_AvramDividend_Classical_chat07_bv_full_jump_kernel_section_integrable
import Theorems.Thm_AvramDividend_Classical_chat07_scale_bv_full_negative_jump_kernel_weight_bound
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Order.Group.Lattice
import Mathlib.Analysis.SpecialFunctions.Exp

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Finite truncated jump first moment makes the weighted absolute scale kernel product integrable. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hWmon : Monotone W)
    (θ : ℝ) (hθ : 0 ≤ θ) (hqθ : q < X.ψ θ)
    (ν : Measure ℝ) [SFinite ν]
    (hνpos : ∀ᵐ r ∂ν, 0 < r)
    (hνmoment : Integrable (fun r : ℝ => min 1 r) ν) :
    Integrable (fun p : ℝ × ℝ =>
      Real.exp (-(θ*p.1)) *
        |W (p.1-p.2) - W p.1 +
          (if p.2 < 1 then p.2*deriv W p.1 else 0)|)
      ((volume.restrict (Ioi (0 : ℝ))).prod ν) := by
  let μ : Measure ℝ := volume.restrict (Ioi (0 : ℝ))
  let C : ℝ :=
    max (θ * (X.ψ θ - q)⁻¹ +
      (∫ x in Ioi (0 : ℝ), Real.exp (-(θ*x)) * deriv W x))
      ((X.ψ θ - q)⁻¹)
  let K : ℝ × ℝ → ℝ := fun p =>
    Real.exp (-(θ*p.1)) *
      |W (p.1-p.2) - W p.1 +
        (if p.2 < 1 then p.2*deriv W p.1 else 0)|
  have hKm : Measurable K :=
    chat07_bv_compensated_kernel_joint_measurable W hWmon θ
  have hKs : StronglyMeasurable K := hKm.stronglyMeasurable
  have hKa : AEStronglyMeasurable K (μ.prod ν) :=
    hKs.aestronglyMeasurable
  have hsections : ∀ᵐ r ∂ν,
      Integrable (fun x : ℝ => K (x,r)) μ := by
    filter_upwards [hνpos] with r hr
    have hs := chat07_bv_full_jump_kernel_section_integrable
      X q W hW θ r hθ hqθ hr
    simpa [K, μ, abs_mul, abs_of_nonneg (Real.exp_nonneg _)] using hs.abs
  have hinner : AEStronglyMeasurable
      (fun r : ℝ => ∫ x : ℝ, ‖K (x,r)‖ ∂μ) ν :=
    (hKs.norm.integral_prod_left' (μ := μ)).aestronglyMeasurable
  have hg : Integrable (fun r : ℝ => min 1 r * C) ν := by
    simpa [mul_comm] using hνmoment.const_mul C
  have hmajor : ∀ᵐ r ∂ν,
      (∫ x : ℝ, ‖K (x,r)‖ ∂μ) ≤ min 1 r * C := by
    filter_upwards [hνpos] with r hr
    have hb := chat07_scale_bv_full_negative_jump_kernel_weight_bound
      X q W hW θ r hθ hqθ hr
    simpa [K, μ, C, Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (Real.exp_nonneg _)] using hb
  exact chat07_product_integrable_of_section_norm_majorant
    μ ν K (fun r => min 1 r * C) hKa hsections hinner hg hmajor
