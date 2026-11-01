-- Prove2me | solution 1 for ExpLaw.cond_mean_below
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-01T02:15:45.43658+00:00
-- url     : https://prove2.me/submissions/b516682a-24fe-43b9-abc1-a024d0b06f36

import Mathlib

open MeasureTheory ProbabilityTheory Filter Topology Asymptotics

namespace CohenPriceFairness.LocalWelfare.Sol_exp_nonbuyer

lemma ec_pdfReal_eq (l x : ℝ) :
    exponentialPDFReal l x = if 0 ≤ x then l * Real.exp (-(l * x)) else 0 := by
  simp [exponentialPDFReal, gammaPDFReal]

lemma ec_pdf_toReal {l : ℝ} (hl : 0 < l) (x : ℝ) :
    (exponentialPDF l x).toReal = exponentialPDFReal l x :=
  ENNReal.toReal_ofReal (exponentialPDFReal_nonneg hl x)

lemma ec_setIntegral {l : ℝ} (hl : 0 < l) (g : ℝ → ℝ) (s : Set ℝ) (hs : MeasurableSet s) :
    ∫ v in s, g v ∂(expMeasure l) = ∫ v in s, exponentialPDFReal l v * g v := by
  change ∫ v in s, g v ∂(volume.withDensity (fun x => exponentialPDF l x)) = _
  rw [setIntegral_withDensity_eq_setIntegral_toReal_smul (f := exponentialPDF l)
      (measurable_exponentialPDFReal l).ennreal_ofReal
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top) _ hs]
  refine setIntegral_congr_fun hs fun v _ => ?_
  rw [smul_eq_mul]
  exact congrArg (· * g v) (ec_pdf_toReal hl v)

instance ec_noAtoms (l : ℝ) : NullSingletonClass (expMeasure l) :=
  ⟨fun x => withDensity_absolutelyContinuous _ _ (measure_singleton x)⟩

lemma ec_Iic_real {l : ℝ} (hl : 0 < l) {p : ℝ} (hp : 0 ≤ p) :
    (expMeasure l).real (Set.Iic p) = 1 - Real.exp (-(l * p)) := by
  have := isProbabilityMeasure_expMeasure hl
  rw [← cdf_eq_real, cdf_expMeasure_eq hl, if_pos hp]

end CohenPriceFairness.LocalWelfare.Sol_exp_nonbuyer

open CohenPriceFairness.LocalWelfare
open CohenPriceFairness.LocalWelfare.Sol_exp_nonbuyer

theorem solution {l p : ℝ} (hl : 0 < l) (hp : 0 < p) :
    (if (expMeasure l) (Set.Iio p) = 0 then 0
      else (∫ v in Set.Iio p, v ∂(expMeasure l)) / ((expMeasure l) (Set.Iio p)).toReal) =
      1 / l - p / (Real.exp (l * p) - 1) := by
  have := isProbabilityMeasure_expMeasure hl
  have hIio : ((expMeasure l) (Set.Iio p)).toReal = 1 - Real.exp (-(l * p)) := by
    rw [measure_congr Iio_ae_eq_Iic]
    exact ec_Iic_real hl hp.le
  have hE : Real.exp (-(l * p)) < 1 := Real.exp_lt_one_iff.mpr (by nlinarith)
  have hne : (expMeasure l) (Set.Iio p) ≠ 0 := by
    intro h
    rw [h] at hIio
    simp at hIio
    linarith
  rw [if_neg hne, hIio, ec_setIntegral hl _ _ measurableSet_Iio]
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Iio
    (s := Set.Ioo 0 p) Set.Ioo_subset_Iio_self
    (fun x hx => by
      simp only [Set.mem_sdiff, Set.mem_Iio, Set.mem_Ioo, not_and] at hx
      by_cases h0 : 0 ≤ x
      · have : x = 0 := by
          by_contra hx0
          have := hx.2 (lt_of_le_of_ne h0 (Ne.symm hx0))
          linarith [hx.1]
        rw [this, mul_zero]
      · rw [ec_pdfReal_eq, if_neg h0, zero_mul])]
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hp.le]
  rw [intervalIntegral.integral_congr (g := fun x => x * l * Real.exp (-(l * x))) (fun x hx => by
    rw [Set.uIcc_of_le hp.le] at hx
    simp only
    rw [ec_pdfReal_eq, if_pos hx.1]
    ring)]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun x => -(x + 1 / l) * Real.exp (-(l * x)))
    (fun x _ => by
      have h : HasDerivAt (fun y => (-1 * (y + 1 / l)) * Real.exp (-l * y))
          (-1 * 1 * Real.exp (-l * x) + -1 * (x + 1 / l) * (Real.exp (-l * x) * (-l * 1))) x :=
        ((((hasDerivAt_id' x).add_const (1 / l))).const_mul (-1)).mul
          (((hasDerivAt_id' x).const_mul (-l)).exp)
      have e : (fun x => -(x + 1 / l) * Real.exp (-(l * x))) =
          (fun y => (-1 * (y + 1 / l)) * Real.exp (-l * y)) := by
        funext y; rw [neg_mul l y]; ring
      rw [e]
      refine h.congr_deriv ?_
      rw [neg_mul l x]
      field_simp
      ring)
    (Continuous.intervalIntegrable (by fun_prop) _ _)]
  have hEp : 1 < Real.exp (l * p) := Real.one_lt_exp_iff.mpr (by positivity)
  simp only [mul_zero, neg_zero, Real.exp_zero, zero_add, mul_one]
  rw [Real.exp_neg]
  have h1 : Real.exp (l * p) - 1 ≠ 0 := by linarith
  have h2 : 1 - (Real.exp (l * p))⁻¹ ≠ 0 := by
    have : (Real.exp (l * p))⁻¹ < 1 := inv_lt_one_of_one_lt₀ hEp
    linarith
  have h3 : Real.exp (l * p) ≠ 0 := (Real.exp_pos _).ne'
  have key : 1 - (Real.exp (l * p))⁻¹ = (Real.exp (l * p) - 1) / Real.exp (l * p) := by
    field_simp
  rw [key]
  field_simp
  rw [mul_comm p l] at *
  rw [eq_sub_iff_add_eq, ← add_div, div_eq_one_iff_eq h1]
  ring
