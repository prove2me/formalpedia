-- Prove2me | solution 1 for FunctionalInequalities.ProductVariance.decomposition_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:39:54.552217+00:00
-- url     : https://prove2.me/submissions/9d1218a7-d8e3-45c5-816b-9c299e356fbf

import Definitions.Def_KLSModular_FunctionalInequalities_Probability_ProductVariance

noncomputable section
open MeasureTheory ProbabilityTheory
variable {E F : Type*} [MeasurableSpace E] [MeasurableSpace F]
  {μ : MeasureTheory.Measure E} {ν : MeasureTheory.Measure F} [MeasureTheory.IsProbabilityMeasure μ] [MeasureTheory.IsProbabilityMeasure ν]
  {f : E × F → ℝ}
/-- Source: local a.e. section helper from Mathlib's `Integrable.prod_right_ae` and
`memLp_two_iff_integrable_sq`, with a.e. strong measurability of sections. -/
theorem FunctionalInequalities.ProductVariance.memLp_right_ae (hf : MemLp f 2 (μ.prod ν)) :
    ∀ᵐ x ∂μ, MemLp (fun y ↦ f (x, y)) 2 ν := by
  filter_upwards [hf.aestronglyMeasurable.prodMk_left, hf.integrable_sq.prod_right_ae]
    with x hm hi
  exact (memLp_two_iff_integrable_sq hm).mpr hi
/-- Jensen's square inequality, with its necessary square-integrability hypothesis.
Source: local consequence of Mathlib's `variance_nonneg` and `variance_eq_sub`. -/
theorem FunctionalInequalities.ProductVariance.sq_integral_le {g : E → ℝ} (hg : MemLp g 2 μ) :
    (∫ x, g x ∂μ) ^ 2 ≤ ∫ x, g x ^ 2 ∂μ := by
  have h0 := variance_nonneg g μ
  rw [variance_eq_sub hg] at h0
  simp only [Pi.pow_apply] at h0
  linarith
/-- Source: local averaging helper from `memLp_right_ae`, `sq_integral_le`, and Mathlib's
`AEStronglyMeasurable.integral_prod_right'` and `Integrable.integral_prod_left`. -/
theorem FunctionalInequalities.ProductVariance.memLp_integral_right (hf : MemLp f 2 (μ.prod ν)) :
    MemLp (fun x ↦ ∫ y, f (x, y) ∂ν) 2 μ := by
  have hsm : AEStronglyMeasurable (fun x ↦ ∫ y, f (x, y) ∂ν) μ :=
    hf.aestronglyMeasurable.integral_prod_right'
  rw [memLp_two_iff_integrable_sq hsm]
  refine (hf.integrable_sq.integral_prod_left).mono'
    ((hsm.aemeasurable.pow_const 2).aestronglyMeasurable) ?_
  filter_upwards [memLp_right_ae hf] with x hx
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  exact sq_integral_le hx
/-- The law of total variance written using ordinary iterated integrals.
Source: local identity from Mathlib's `variance_eq_sub` and `integral_prod`, with the
section and averaging integrability helpers above. -/
theorem solution (hf : MemLp f 2 (μ.prod ν)) :
    variance f (μ.prod ν) =
      (∫ x, variance (fun y ↦ f (x, y)) ν ∂μ) +
      variance (fun x ↦ ∫ y, f (x, y) ∂ν) μ := by
  have hg : MemLp (fun x ↦ ∫ y, f (x, y) ∂ν) 2 μ := FunctionalInequalities.ProductVariance.memLp_integral_right hf
  have h1 : Integrable (fun x ↦ ∫ y, f (x, y) ^ 2 ∂ν) μ := hf.integrable_sq.integral_prod_left
  have h2 : Integrable (fun x ↦ (∫ y, f (x, y) ∂ν) ^ 2) μ := hg.integrable_sq
  have hVar : (∫ x, variance (fun y ↦ f (x, y)) ν ∂μ)
      = ∫ x, ((∫ y, f (x, y) ^ 2 ∂ν) - (∫ y, f (x, y) ∂ν) ^ 2) ∂μ := by
    apply integral_congr_ae
    filter_upwards [FunctionalInequalities.ProductVariance.memLp_right_ae hf] with x hx
    rw [variance_eq_sub hx]
    simp only [Pi.pow_apply]
  have hsq : (∫ p, f p ^ 2 ∂μ.prod ν) = ∫ x, ∫ y, f (x, y) ^ 2 ∂ν ∂μ :=
    integral_prod _ hf.integrable_sq
  have hmean : (∫ p, f p ∂μ.prod ν) = ∫ x, ∫ y, f (x, y) ∂ν ∂μ :=
    integral_prod _ (hf.integrable one_le_two)
  rw [hVar, integral_sub h1 h2, variance_eq_sub hf, variance_eq_sub hg]
  simp only [Pi.pow_apply]
  rw [hsq, hmean]
  ring
