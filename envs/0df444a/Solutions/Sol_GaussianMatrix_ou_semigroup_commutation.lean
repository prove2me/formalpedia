-- Prove2me | solution 1 for GaussianMatrix.ou_semigroup_commutation
-- status  : ACCEPTED   (prove)
-- author  : @tc
-- created : 2026-10-09T08:20:27.267786+00:00
-- url     : https://prove2.me/submissions/938279dc-3a55-488c-97b8-76fe669f383a

import Definitions.Def_GaussianMatrix_basic

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace GaussianMatrix

lemma integrable_abs_id_gaussian : Integrable (fun y : ℝ => |y|) (gaussianReal 0 1) := by
  have : Integrable (fun y : ℝ => y) (gaussianReal 0 1) :=
    memLp_one_iff_integrable.1 (memLp_id_gaussianReal 1)
  exact this.abs

/-- A function with bounded derivative has linear growth. -/
lemma abs_le_of_deriv_bound (f : ℝ → ℝ) (hf : Differentiable ℝ f) (C : ℝ)
    (hdf : ∀ x, |deriv f x| ≤ C) (z : ℝ) : |f z| ≤ |f 0| + C * |z| := by
  have := Convex.norm_image_sub_le_of_norm_deriv_le (f := f) (s := Set.univ) (C := C)
    (fun x _ => hf x) (fun x _ => by simpa using hdf x) convex_univ (Set.mem_univ 0)
    (Set.mem_univ z)
  simp only [Real.norm_eq_abs, sub_zero] at this
  have h2 := abs_sub_abs_le_abs_sub (f z) (f 0)
  linarith

lemma integrable_comp_affine_of_deriv_bound (f : ℝ → ℝ) (hf : Differentiable ℝ f) (C : ℝ)
    (hdf : ∀ x, |deriv f x| ≤ C) (c d : ℝ) :
    Integrable (fun y => f (c + d * y)) (gaussianReal 0 1) := by
  have hC : 0 ≤ C := le_trans (abs_nonneg _) (hdf 0)
  refine Integrable.mono' ((integrable_const (|f 0| + C * |c|)).add
    (integrable_abs_id_gaussian.const_mul (C * |d|))) ?_ ?_
  · exact (hf.continuous.comp (by fun_prop)).aestronglyMeasurable
  · refine Filter.Eventually.of_forall (fun y => ?_)
    rw [Real.norm_eq_abs]
    refine (abs_le_of_deriv_bound f hf C hdf _).trans ?_
    have : |c + d * y| ≤ |c| + |d| * |y| := by
      rw [← abs_mul]; exact abs_add_le _ _
    simp only [Pi.add_apply]
    nlinarith

end GaussianMatrix

open GaussianMatrix

theorem solution (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f) (C : ℝ)
    (hdf : ∀ x, |deriv f x| ≤ C) (t x : ℝ) :
    HasDerivAt
      (fun z => ∫ y, f (Real.exp (-t) * z + Real.sqrt (1 - Real.exp (-(2 * t))) * y)
        ∂(gaussianReal 0 1))
      (Real.exp (-t) * ∫ y, deriv f (Real.exp (-t) * x + Real.sqrt (1 - Real.exp (-(2 * t))) * y)
        ∂(gaussianReal 0 1)) x := by
  set a := Real.exp (-t)
  set b := Real.sqrt (1 - Real.exp (-(2 * t)))
  have hfd : Differentiable ℝ f := hf.differentiable one_ne_zero
  have hfc : Continuous (deriv f) := hf.continuous_deriv le_rfl
  rw [← integral_const_mul]
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := gaussianReal 0 1)
    (F := fun z y => f (a * z + b * y)) (F' := fun z y => a * deriv f (a * z + b * y))
    (x₀ := x) (bound := fun _ => |a| * C) Filter.univ_mem ?_ ?_ ?_ ?_ ?_ ?_).2
  · exact Filter.Eventually.of_forall (fun z =>
      (hfd.continuous.comp (by fun_prop)).aestronglyMeasurable)
  · exact integrable_comp_affine_of_deriv_bound f hfd C hdf (a * x) b
  · exact ((hfc.comp (by fun_prop)).const_mul a).aestronglyMeasurable
  · refine Filter.Eventually.of_forall (fun y z _ => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_left (hdf _) (abs_nonneg _)
  · exact integrable_const _
  · refine Filter.Eventually.of_forall (fun y z _ => ?_)
    have h1 : HasDerivAt (fun z => a * z + b * y) a z := by
      simpa using ((hasDerivAt_id z).const_mul a).add_const (b * y)
    have := (hfd (a * z + b * y)).hasDerivAt.comp z h1
    rw [mul_comm (deriv f _) a] at this
    exact this
