-- Prove2me | solution 1 for GaussianMatrix.gaussian_ibp_one_dim
-- status  : ACCEPTED   (prove)
-- author  : @tc
-- created : 2026-10-09T08:09:52.085628+00:00
-- url     : https://prove2.me/submissions/5b731113-a4cb-4c56-a82d-01d87a09b4d2

import Definitions.Def_GaussianMatrix_basic

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace GaussianMatrix

lemma integrable_gaussian_iff (g : ℝ → ℝ) :
    Integrable g (gaussianReal 0 1) ↔ Integrable (fun x => gaussianPDFReal 0 1 x * g x) := by
  rw [gaussianReal_of_var_ne_zero _ one_ne_zero,
    integrable_withDensity_iff_integrable_smul' (measurable_gaussianPDF _ _)
      (ae_of_all _ fun _ => gaussianPDF_lt_top)]
  simp [smul_eq_mul]

lemma integrable_abs_id_gaussian' : Integrable (fun y : ℝ => |y|) (gaussianReal 0 1) := by
  have : Integrable (fun y : ℝ => y) (gaussianReal 0 1) :=
    memLp_one_iff_integrable.1 (memLp_id_gaussianReal 1)
  exact this.abs

lemma integrable_sq_id_gaussian : Integrable (fun y : ℝ => y ^ 2) (gaussianReal 0 1) := by
  have := (memLp_id_gaussianReal (μ := 0) (v := 1) 2).integrable_norm_pow (by norm_num)
  simpa using this

lemma abs_le_of_deriv_bound' (f : ℝ → ℝ) (hf : Differentiable ℝ f) (C : ℝ)
    (hdf : ∀ x, |deriv f x| ≤ C) (z : ℝ) : |f z| ≤ |f 0| + C * |z| := by
  have := Convex.norm_image_sub_le_of_norm_deriv_le (f := f) (s := Set.univ) (C := C)
    (fun x _ => hf x) (fun x _ => by simpa using hdf x) convex_univ (Set.mem_univ 0)
    (Set.mem_univ z)
  simp only [Real.norm_eq_abs, sub_zero] at this
  have h2 := abs_sub_abs_le_abs_sub (f z) (f 0)
  linarith

lemma gaussianPDFReal_zero_one_eq :
    gaussianPDFReal 0 1 = fun x => (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(x ^ 2) / 2) := by
  funext x; simp [gaussianPDFReal_def]

lemma hasDerivAt_gaussianPDFReal_zero_one (x : ℝ) :
    HasDerivAt (gaussianPDFReal 0 1) (-(x * gaussianPDFReal 0 1 x)) x := by
  rw [gaussianPDFReal_zero_one_eq]
  have h1 : HasDerivAt (fun x : ℝ => -(x ^ 2) / 2) (-x) x :=
    (((hasDerivAt_pow 2 x).neg).div_const 2).congr_deriv (by norm_num; ring)
  exact ((h1.exp).const_mul (Real.sqrt (2 * Real.pi))⁻¹).congr_deriv (by ring)

end GaussianMatrix

open GaussianMatrix

theorem solution (h : ℝ → ℝ) (hh : Differentiable ℝ h) (C : ℝ)
    (hdh : ∀ x, |deriv h x| ≤ C) :
    ∫ x, x * h x ∂(gaussianReal 0 1) = ∫ x, deriv h x ∂(gaussianReal 0 1) := by
  have hC : 0 ≤ C := le_trans (abs_nonneg _) (hdh 0)
  set φ := gaussianPDFReal 0 1
  have hhc : Continuous h := hh.continuous
  -- integrability facts under γ
  have hxh : Integrable (fun x => x * h x) (gaussianReal 0 1) := by
    refine Integrable.mono' ((integrable_abs_id_gaussian'.const_mul |h 0|).add
      (integrable_sq_id_gaussian.const_mul C)) (by fun_prop) ?_
    refine Filter.Eventually.of_forall (fun x => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    have := abs_le_of_deriv_bound' h hh C hdh x
    have hx := abs_nonneg x
    simp only [Pi.add_apply]
    rw [← sq_abs x]
    nlinarith
  have hdm : Measurable (deriv h) := measurable_deriv h
  have hdi : Integrable (deriv h) (gaussianReal 0 1) := by
    refine Integrable.mono' (integrable_const C) hdm.aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall (fun x => by rw [Real.norm_eq_abs]; exact hdh x)
  have hhi : Integrable h (gaussianReal 0 1) := by
    refine Integrable.mono' ((integrable_const |h 0|).add
      (integrable_abs_id_gaussian'.const_mul C)) hhc.aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall (fun x => by
      rw [Real.norm_eq_abs]; exact abs_le_of_deriv_bound' h hh C hdh x)
  rw [integrable_gaussian_iff] at hxh hdi hhi
  rw [integral_gaussianReal_eq_integral_smul one_ne_zero,
    integral_gaussianReal_eq_integral_smul one_ne_zero]
  simp only [smul_eq_mul]
  -- integration by parts on the line with `u = h`, `v = -φ`, `v' = x φ`
  have key := integral_mul_deriv_eq_deriv_mul_of_integrable (u := h) (v := fun x => -φ x)
    (u' := deriv h) (v' := fun x => x * φ x)
    (fun x _ => (hh x).hasDerivAt)
    (fun x _ => ((hasDerivAt_gaussianPDFReal_zero_one x).neg).congr_deriv (by ring))
    (by
      have : (h * fun x => x * φ x) = fun x => φ x * (x * h x) := by funext x; simp; ring
      rw [this]; exact hxh)
    (by
      have : (deriv h * fun x => -φ x) = fun x => -(φ x * deriv h x) := by funext x; simp; ring
      rw [this]; exact hdi.neg)
    (by
      have : (h * fun x => -φ x) = fun x => -(φ x * h x) := by funext x; simp; ring
      rw [this]; exact hhi.neg)
  have e1 : (fun x => φ x * (x * h x)) = fun x => h x * (x * φ x) := by funext x; ring
  have e2 : (fun x => φ x * deriv h x) = fun x => -(deriv h x * -φ x) := by funext x; ring
  rw [e1, key, e2, integral_neg]
