-- Prove2me | solution 1 for FunctionalInequalities.Analysis.BakryEmery.laplacian_mul_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T14:46:13.966205+00:00
-- url     : https://prove2.me/submissions/4fccd635-1a5c-4e1e-8d79-e79d9354a924

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Calculus
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Laplacian

noncomputable section
open InnerProductSpace
open scoped ContDiff RealInnerProductSpace
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
section
namespace FunctionalInequalities.Analysis.BakryEmery
end FunctionalInequalities.Analysis.BakryEmery
open FunctionalInequalities FunctionalInequalities.Analysis FunctionalInequalities.Analysis.BakryEmery
universe u
section DifferentialTools
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
section Directional
/-- Product rule for directional derivatives. -/
theorem FunctionalInequalities.Analysis.BakryEmery.fderiv_mul_apply {f g : E → ℝ} {x : E} (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) (v : E) :
    fderiv ℝ (fun y => f y * g y) x v = f x * fderiv ℝ g x v + g x * fderiv ℝ f x v := by
  rw [fderiv_fun_mul hf hg]
  simp
/-- Sum rule for directional derivatives. -/
theorem FunctionalInequalities.Analysis.BakryEmery.fderiv_add_apply {f g : E → ℝ} {x : E} (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) (v : E) :
    fderiv ℝ (fun y => f y + g y) x v = fderiv ℝ f x v + fderiv ℝ g x v := by
  rw [fderiv_fun_add hf hg]
  simp
end Directional
section StdBasis
variable [FiniteDimensional ℝ E]
variable [CompleteSpace E]
omit [CompleteSpace E] in
/-- The Laplacian as the trace of the iterated directional derivatives, at a point where the
derivative is differentiable. -/
theorem FunctionalInequalities.Analysis.BakryEmery.laplacian_eq_sum_fderiv_apply_fderiv_apply {g : E → ℝ} {x : E}
    (hg : DifferentiableAt ℝ (fderiv ℝ g) x) :
    Laplacian.laplacian g x =
      ∑ i, fderiv ℝ (fun y => fderiv ℝ g y (stdOrthonormalBasis ℝ E i)) x
        (stdOrthonormalBasis ℝ E i) := by
  rw [laplacian_eq_sum_fderiv_fderiv]
  exact Finset.sum_congr rfl fun i _ => (fderiv_fderiv_apply hg _ _).symm
namespace FunctionalInequalities.Analysis.BakryEmery
end FunctionalInequalities.Analysis.BakryEmery
open FunctionalInequalities.Analysis.BakryEmery in
/-- Product rule for the Laplacian: `Δ(fg) = f Δg + g Δf + 2 ⟪∇f, ∇g⟫`. -/
theorem solution {f g : E → ℝ} (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (x : E) :
    Laplacian.laplacian (fun y => f y * g y) x =
      f x * Laplacian.laplacian g x + g x * Laplacian.laplacian f x +
        2 * ⟪gradient f x, gradient g x⟫ := by
  have hfg : ContDiff ℝ 2 (fun y => f y * g y) := hf.mul hg
  have hfd : ∀ y, DifferentiableAt ℝ f y := fun y => hf.differentiable (by norm_num) y
  have hgd : ∀ y, DifferentiableAt ℝ g y := fun y => hg.differentiable (by norm_num) y
  rw [FunctionalInequalities.Analysis.BakryEmery.laplacian_eq_sum_fderiv_apply_fderiv_apply
    ((hfg.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero x),
    FunctionalInequalities.Analysis.BakryEmery.laplacian_eq_sum_fderiv_apply_fderiv_apply
    ((hf.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero x),
    FunctionalInequalities.Analysis.BakryEmery.laplacian_eq_sum_fderiv_apply_fderiv_apply
    ((hg.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero x),
    FunctionalInequalities.Analysis.BakryEmery.inner_gradient_eq_sum_fderiv_mul_fderiv]
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h1 : (fun y => fderiv ℝ (fun z => f z * g z) y (stdOrthonormalBasis ℝ E i)) =
      fun y => f y * fderiv ℝ g y (stdOrthonormalBasis ℝ E i) +
        g y * fderiv ℝ f y (stdOrthonormalBasis ℝ E i) :=
    funext fun y => FunctionalInequalities.Analysis.BakryEmery.fderiv_mul_apply (hfd y) (hgd y) _
  have hA : DifferentiableAt ℝ (fun y => f y * fderiv ℝ g y (stdOrthonormalBasis ℝ E i)) x :=
    (hfd x).mul (FunctionalInequalities.Analysis.BakryEmery.differentiable_fderiv_apply hg _ x)
  have hB : DifferentiableAt ℝ (fun y => g y * fderiv ℝ f y (stdOrthonormalBasis ℝ E i)) x :=
    (hgd x).mul (FunctionalInequalities.Analysis.BakryEmery.differentiable_fderiv_apply hf _ x)
  rw [h1, FunctionalInequalities.Analysis.BakryEmery.fderiv_add_apply hA hB, FunctionalInequalities.Analysis.BakryEmery.fderiv_mul_apply (hfd x) (FunctionalInequalities.Analysis.BakryEmery.differentiable_fderiv_apply hg _ x),
    FunctionalInequalities.Analysis.BakryEmery.fderiv_mul_apply (hgd x) (FunctionalInequalities.Analysis.BakryEmery.differentiable_fderiv_apply hf _ x)]
  ring
