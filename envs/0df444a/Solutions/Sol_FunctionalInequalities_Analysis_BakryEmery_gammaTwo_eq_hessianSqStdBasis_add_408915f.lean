-- Prove2me | solution 1 for FunctionalInequalities.Analysis.BakryEmery.gammaTwo_eq_hessianSqStdBasis_add_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T14:42:25.200755+00:00
-- url     : https://prove2.me/submissions/917757ee-a6c7-4d11-8629-e355cb720814

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Bochner_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Calculus
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Gamma
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Laplacian
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_inner_gradient_gradient_inner_408915f
import Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_inner_gradient_gradient_laplacian_408915f
import Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_laplacian_norm_gradient_sq_408915f

section
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
theorem FunctionalInequalities.Analysis.BakryEmery.fderiv_sum_apply {ι : Type*} (s : Finset ι) {g : ι → E → ℝ} {x : E}
    (hg : ∀ i ∈ s, DifferentiableAt ℝ (g i) x) (v : E) :
    fderiv ℝ (fun y => ∑ i ∈ s, g i y) x v = ∑ i ∈ s, fderiv ℝ (g i) x v := by
  rw [fderiv_fun_sum hg]
  simp
end Directional
section Gradient
variable [CompleteSpace E]
/-- The gradient of a `C^n` function is `C^m` when `m + 1 ≤ n`. -/
theorem FunctionalInequalities.Analysis.BakryEmery.contDiff_gradient {f : E → ℝ} {n m : WithTop ℕ∞} (hf : ContDiff ℝ n f) (hmn : m + 1 ≤ n) :
    ContDiff ℝ m (gradient f) :=
  (toDual ℝ E).symm.contDiff.comp (hf.fderiv_right hmn)
/-- Difference rule for the gradient. -/
theorem FunctionalInequalities.Analysis.BakryEmery.gradient_sub {f g : E → ℝ} {x : E} (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) :
    gradient (fun y => f y - g y) x = gradient f x - gradient g x := by
  unfold gradient
  rw [fderiv_fun_sub hf hg, map_sub]
end Gradient
section StdBasis
variable [FiniteDimensional ℝ E]
variable [CompleteSpace E]
/-- `‖∇f‖²` is the sum of the squared directional derivatives in the standard orthonormal basis. -/
theorem FunctionalInequalities.Analysis.BakryEmery.norm_gradient_sq_eq_sum (f : E → ℝ) (y : E) :
    ‖gradient f y‖ ^ 2 = ∑ i, fderiv ℝ f y (stdOrthonormalBasis ℝ E i) ^ 2 := by
  rw [← (stdOrthonormalBasis ℝ E).sum_sq_inner_left]
  simp only [inner_gradient_left]
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
omit [CompleteSpace E] in
/-- The Laplacian of a `C²` function as a function: the trace of the iterated directional
derivatives in the standard orthonormal basis. -/
theorem FunctionalInequalities.Analysis.BakryEmery.laplacian_eq_fun_sum {g : E → ℝ} (hg : ContDiff ℝ 2 g) :
    Laplacian.laplacian g = fun x =>
      ∑ i, fderiv ℝ (fun y => fderiv ℝ g y (stdOrthonormalBasis ℝ E i)) x
        (stdOrthonormalBasis ℝ E i) :=
  funext fun x => laplacian_eq_sum_fderiv_apply_fderiv_apply
    ((hg.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero x)
omit [CompleteSpace E] in
/-- The Laplacian of a `C^n` function is `C^m` when `m + 2 ≤ n`. -/
theorem FunctionalInequalities.Analysis.BakryEmery.contDiff_laplacian {g : E → ℝ} {n m : WithTop ℕ∞} (hg : ContDiff ℝ n g) (hmn : m + 2 ≤ n) :
    ContDiff ℝ m (Laplacian.laplacian g) := by
  have h2 : (2 : WithTop ℕ∞) ≤ n := le_trans (by simp) hmn
  rw [laplacian_eq_fun_sum (hg.of_le h2)]
  refine ContDiff.sum fun i _ => ?_
  refine contDiff_fderiv_apply (contDiff_fderiv_apply hg ?_ _) le_rfl _
  calc m + 1 + 1 = m + 2 := by rw [add_assoc]; norm_num
    _ ≤ n := hmn
end StdBasis
end DifferentialTools
end
end
end
end
end

section
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
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
section Gamma
variable [CompleteSpace E]
theorem FunctionalInequalities.Analysis.BakryEmery.gamma_apply (f g : E → ℝ) (x : E) : gamma f g x = ⟪gradient f x, gradient g x⟫ := rfl
/-- `Γ(f, f) = ‖∇f‖²`: the normalisation of `Γ` carries no extra factor. -/
theorem FunctionalInequalities.Analysis.BakryEmery.gamma_self (f : E → ℝ) (x : E) : gamma f f x = ‖gradient f x‖ ^ 2 :=
  real_inner_self_eq_norm_sq _
variable [FiniteDimensional ℝ E]
theorem FunctionalInequalities.Analysis.BakryEmery.gammaTwo_apply (U f : E → ℝ) (x : E) :
    gammaTwo U f x =
      weightedLaplacian U (fun y => gamma f f y) x / 2 - gamma f (weightedLaplacian U f) x := rfl
/-- `Γ₂` written out in gradients and Laplacians, exactly the left-hand side of route the Bochner identity. -/
theorem FunctionalInequalities.Analysis.BakryEmery.gammaTwo_eq_expanded (U f : E → ℝ) (x : E) :
    gammaTwo U f x =
      (Laplacian.laplacian (fun y => ‖gradient f y‖ ^ 2) x -
          ⟪gradient U x, gradient (fun y => ‖gradient f y‖ ^ 2) x⟫) / 2 -
        ⟪gradient f x,
          gradient (fun y => Laplacian.laplacian f y - ⟪gradient U y, gradient f y⟫) x⟫ := by
  simp only [gammaTwo_apply, gamma_self, weightedLaplacian_apply, gamma_apply]
  rfl
end Gamma
end
end
end
end
end

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
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
section HessianSq
variable [FiniteDimensional ℝ E]
theorem FunctionalInequalities.Analysis.BakryEmery.hessianSqStdBasis_apply (f : E → ℝ) (x : E) :
    hessianSqStdBasis f x = ∑ i, ∑ j,
      (bilinearIteratedFDerivTwo ℝ f x (stdOrthonormalBasis ℝ E i) (stdOrthonormalBasis ℝ E j)) ^ 2 :=
  rfl
end HessianSq
section Terms
variable [CompleteSpace E] [FiniteDimensional ℝ E]
/-- `‖∇f‖²` as a sum of products of directional derivatives. -/
theorem FunctionalInequalities.Analysis.BakryEmery.norm_gradient_sq_fun (f : E → ℝ) :
    (fun y => ‖gradient f y‖ ^ 2) = fun y =>
      ∑ j, fderiv ℝ f y (stdOrthonormalBasis ℝ E j) * fderiv ℝ f y (stdOrthonormalBasis ℝ E j) :=
  funext fun y => by rw [norm_gradient_sq_eq_sum]; simp only [sq]
/-- The directional derivative of `‖∇f‖²`: `∂ᵥ‖∇f‖² = 2 ∑ⱼ ∂ⱼf ∂ᵥ∂ⱼf`. -/
theorem FunctionalInequalities.Analysis.BakryEmery.fderiv_norm_gradient_sq_apply {f : E → ℝ} (hf : ContDiff ℝ 2 f) (x v : E) :
    fderiv ℝ (fun y => ‖gradient f y‖ ^ 2) x v =
      2 * ∑ j, fderiv ℝ f x (stdOrthonormalBasis ℝ E j) *
        fderiv ℝ (fun y => fderiv ℝ f y (stdOrthonormalBasis ℝ E j)) x v := by
  rw [norm_gradient_sq_fun]
  have hd : ∀ j ∈ (Finset.univ : Finset (Fin (Module.finrank ℝ E))), DifferentiableAt ℝ
      (fun y => fderiv ℝ f y (stdOrthonormalBasis ℝ E j) * fderiv ℝ f y (stdOrthonormalBasis ℝ E j))
      x := fun j _ => (differentiable_fderiv_apply hf _ x).mul (differentiable_fderiv_apply hf _ x)
  rw [fderiv_sum_apply _ hd, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [fderiv_mul_apply (differentiable_fderiv_apply hf _ x) (differentiable_fderiv_apply hf _ x)]
  ring
/-- Drift term: `⟪∇U, ∇‖∇f‖²⟫ = 2 ∑ᵢ ∑ⱼ ∂ᵢU ∂ⱼf D²f(eᵢ, eⱼ)`. -/
theorem FunctionalInequalities.Analysis.BakryEmery.inner_gradient_gradient_norm_sq (U : E → ℝ) {f : E → ℝ} (hf : ContDiff ℝ 2 f) (x : E) :
    ⟪gradient U x, gradient (fun y => ‖gradient f y‖ ^ 2) x⟫ =
      2 * ∑ i, ∑ j, fderiv ℝ U x (stdOrthonormalBasis ℝ E i) *
        fderiv ℝ f x (stdOrthonormalBasis ℝ E j) *
        bilinearIteratedFDerivTwo ℝ f x (stdOrthonormalBasis ℝ E i) (stdOrthonormalBasis ℝ E j) := by
  rw [inner_gradient_eq_sum_fderiv_mul_fderiv, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [fderiv_norm_gradient_sq_apply hf, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [bilinearIteratedFDerivTwo_eq_fderiv_apply hf]
  ring
end Terms
section Bochner
variable [CompleteSpace E] [FiniteDimensional ℝ E]
namespace FunctionalInequalities.Analysis.BakryEmery
end FunctionalInequalities.Analysis.BakryEmery
open FunctionalInequalities.Analysis.BakryEmery in
/-- **the Bochner identity, the Bochner identity in the standard orthonormal basis**: for `C²` `U` and `C³`
`f`, `Γ₂(f) = ∑ᵢ ∑ⱼ (D²f(eᵢ, eⱼ))² + D²U(∇f, ∇f)`. -/
theorem solution {U f : E → ℝ} (hU : ContDiff ℝ 2 U)
    (hf : ContDiff ℝ 3 f) (x : E) :
    FunctionalInequalities.Analysis.BakryEmery.gammaTwo U f x =
      FunctionalInequalities.Analysis.BakryEmery.hessianSqStdBasis f x +
        bilinearIteratedFDerivTwo ℝ U x (gradient f x) (gradient f x) := by
  have hf2 : ContDiff ℝ 2 f := hf.of_le (by norm_num)
  have hΔ : DifferentiableAt ℝ (Laplacian.laplacian f) x :=
    (FunctionalInequalities.Analysis.BakryEmery.contDiff_laplacian hf (m := 1) (by norm_num)).differentiable one_ne_zero x
  have hgU : ContDiff ℝ 1 (gradient U) := FunctionalInequalities.Analysis.BakryEmery.contDiff_gradient hU (by norm_num)
  have hgf : ContDiff ℝ 1 (gradient f) := FunctionalInequalities.Analysis.BakryEmery.contDiff_gradient hf (by norm_num)
  have hI : DifferentiableAt ℝ (fun y => ⟪gradient U y, gradient f y⟫) x :=
    (hgU.inner ℝ hgf).differentiable one_ne_zero x
  rw [FunctionalInequalities.Analysis.BakryEmery.gammaTwo_eq_expanded, FunctionalInequalities.Analysis.BakryEmery.gradient_sub hΔ hI, inner_sub_right, FunctionalInequalities.Analysis.BakryEmery.laplacian_norm_gradient_sq_408915f hf,
    FunctionalInequalities.Analysis.BakryEmery.inner_gradient_gradient_norm_sq U hf2, FunctionalInequalities.Analysis.BakryEmery.inner_gradient_gradient_laplacian_408915f hf,
    FunctionalInequalities.Analysis.BakryEmery.inner_gradient_gradient_inner_408915f hU hf2, FunctionalInequalities.Analysis.BakryEmery.hessianSqStdBasis_apply]
  ring
