-- Prove2me | solution 1 for ExpLaw.mean_excess
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-01T02:15:43.858888+00:00
-- url     : https://prove2.me/submissions/f37ca4c3-755d-4a78-982e-40a8d6e4b844

import Mathlib

open MeasureTheory ProbabilityTheory Filter Topology Asymptotics

namespace CohenPriceFairness.LocalWelfare.Sol_exp_surplus

lemma ec_pdfReal_eq (l x : ℝ) :
    exponentialPDFReal l x = if 0 ≤ x then l * Real.exp (-(l * x)) else 0 := by
  simp [exponentialPDFReal, gammaPDFReal]

lemma ec_pdf_toReal {l : ℝ} (hl : 0 < l) (x : ℝ) :
    (exponentialPDF l x).toReal = exponentialPDFReal l x :=
  ENNReal.toReal_ofReal (exponentialPDFReal_nonneg hl x)

lemma ec_integral {l : ℝ} (hl : 0 < l) (g : ℝ → ℝ) :
    ∫ v, g v ∂(expMeasure l) = ∫ v, exponentialPDFReal l v * g v := by
  change ∫ v, g v ∂(volume.withDensity (exponentialPDF l)) = _
  rw [integral_withDensity_eq_integral_toReal_smul (f := exponentialPDF l)
      (measurable_exponentialPDFReal l).ennreal_ofReal
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  congr 1
  funext v
  rw [smul_eq_mul]
  exact congrArg (· * g v) (ec_pdf_toReal hl v)

end CohenPriceFairness.LocalWelfare.Sol_exp_surplus

open CohenPriceFairness.LocalWelfare
open CohenPriceFairness.LocalWelfare.Sol_exp_surplus

theorem solution {l p : ℝ} (hl : 0 < l) (hp : 0 ≤ p) :
    ∫ v, max (v - p) 0 ∂(expMeasure l) = Real.exp (-(l * p)) / l := by
  rw [ec_integral hl]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Set.Ioi p) (fun x hx => by
    simp only [Set.mem_Ioi, not_lt] at hx
    rw [max_eq_right (by linarith), mul_zero])]
  rw [setIntegral_congr_fun measurableSet_Ioi (g := fun x => (x - p) * l * Real.exp (-(l * x)))
    (fun x hx => by
      simp only [Set.mem_Ioi] at hx
      rw [ec_pdfReal_eq, if_pos (by linarith), max_eq_left (by linarith)]
      ring)]
  have key := integral_Ioi_of_hasDerivAt_of_nonneg' (a := p) (l := 0)
    (g := fun x => -(x - p + 1 / l) * Real.exp (-(l * x)))
    (g' := fun x => (x - p) * l * Real.exp (-(l * x)))
    (fun x _ => by
      have h : HasDerivAt (fun y => (-1 * (y - p + 1 / l)) * Real.exp (-l * y))
          (-1 * 1 * Real.exp (-l * x) + -1 * (x - p + 1 / l) * (Real.exp (-l * x) * (-l * 1))) x :=
        ((((hasDerivAt_id' x).sub_const p).add_const (1 / l)).const_mul (-1)).mul
          (((hasDerivAt_id' x).const_mul (-l)).exp)
      have e : (fun x => -(x - p + 1 / l) * Real.exp (-(l * x))) =
          (fun y => (-1 * (y - p + 1 / l)) * Real.exp (-l * y)) := by
        funext y; rw [neg_mul l y]; ring
      rw [e]
      refine h.congr_deriv ?_
      rw [neg_mul l x]
      field_simp
      ring)
    (fun x hx => by
      simp only [Set.mem_Ioi] at hx
      have := Real.exp_pos (-(l * x))
      have : 0 ≤ x - p := by linarith
      positivity)
    (by
      have h1 : Tendsto (fun x : ℝ => x ^ (1 : ℝ) * Real.exp (-l * x)) atTop (𝓝 0) :=
        tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 l hl
      have h2 : Tendsto (fun x : ℝ => Real.exp (-(l * x))) atTop (𝓝 0) :=
        Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop hl)
      have h3 := (h1.neg).add (h2.const_mul (p - 1 / l))
      simp only [neg_zero, mul_zero, add_zero] at h3
      refine h3.congr fun x => ?_
      simp only [Real.rpow_one, neg_mul]
      ring)
  rw [key]
  field_simp
  ring
