-- Prove2me | solution 1 for FunctionalInequalities.Analysis.BakryEmery.laplacian_norm_gradient_sq_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T14:41:17.975787+00:00
-- url     : https://prove2.me/submissions/2d9d6728-fffb-42d1-9a86-44a649adc24a

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
/-- Directional derivative of a constant multiple. -/
theorem FunctionalInequalities.Analysis.BakryEmery.fderiv_const_mul_apply {g : E → ℝ} {x : E} (hg : DifferentiableAt ℝ g x) (c : ℝ) (v : E) :
    fderiv ℝ (fun y => c * g y) x v = c * fderiv ℝ g x v := by
  rw [fderiv_const_mul hg c]
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
end StdBasis
end DifferentialTools
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
section Sums
variable {ι : Type*} [Fintype ι]
theorem FunctionalInequalities.Analysis.BakryEmery.sum_two_mul_sum_add (p : ι → ι → ℝ) (a : ι → ℝ) (c : ι → ι → ℝ) :
    ∑ i, 2 * ∑ j, (p i j + a j * c i j) =
      2 * ∑ i, ∑ j, p i j + 2 * ∑ j, a j * ∑ i, c i j := by
  simp only [Finset.mul_sum, mul_add, Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_comm]
end Sums
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
namespace FunctionalInequalities.Analysis.BakryEmery
end FunctionalInequalities.Analysis.BakryEmery
open FunctionalInequalities.Analysis.BakryEmery in
/-- Laplacian of `‖∇f‖²`: `Δ‖∇f‖² = 2 ∑ᵢ ∑ⱼ (D²f(eᵢ, eⱼ))² + 2 ∑ⱼ ∂ⱼf ∑ᵢ ∂ᵢ∂ᵢ∂ⱼf`. -/
theorem solution {f : E → ℝ} (hf : ContDiff ℝ 3 f) (x : E) :
    Laplacian.laplacian (fun y => ‖gradient f y‖ ^ 2) x =
      2 * ∑ i, ∑ j,
          (bilinearIteratedFDerivTwo ℝ f x (stdOrthonormalBasis ℝ E i)
            (stdOrthonormalBasis ℝ E j)) ^ 2 +
        2 * ∑ j, fderiv ℝ f x (stdOrthonormalBasis ℝ E j) *
          ∑ i, fderiv ℝ (fun y => fderiv ℝ (fun z => fderiv ℝ f z (stdOrthonormalBasis ℝ E j)) y
            (stdOrthonormalBasis ℝ E i)) x (stdOrthonormalBasis ℝ E i) := by
  have hf2 : ContDiff ℝ 2 f := hf.of_le (by norm_num)
  have hg2 : ContDiff ℝ 2 (gradient f) := FunctionalInequalities.Analysis.BakryEmery.contDiff_gradient hf (by norm_num)
  have hN : ContDiff ℝ 2 (fun y => ‖gradient f y‖ ^ 2) := hg2.norm_sq (𝕜 := ℝ)
  rw [FunctionalInequalities.Analysis.BakryEmery.laplacian_eq_sum_fderiv_apply_fderiv_apply
    ((hN.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero x), ← FunctionalInequalities.Analysis.BakryEmery.sum_two_mul_sum_add]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h1 : (fun y => fderiv ℝ (fun z => ‖gradient f z‖ ^ 2) y (stdOrthonormalBasis ℝ E i)) =
      fun y => 2 * ∑ j, fderiv ℝ f y (stdOrthonormalBasis ℝ E j) *
        fderiv ℝ (fun z => fderiv ℝ f z (stdOrthonormalBasis ℝ E j)) y (stdOrthonormalBasis ℝ E i) :=
    funext fun y => FunctionalInequalities.Analysis.BakryEmery.fderiv_norm_gradient_sq_apply hf2 y _
  have hd : ∀ j ∈ (Finset.univ : Finset (Fin (Module.finrank ℝ E))), DifferentiableAt ℝ
      (fun y => fderiv ℝ f y (stdOrthonormalBasis ℝ E j) *
        fderiv ℝ (fun z => fderiv ℝ f z (stdOrthonormalBasis ℝ E j)) y (stdOrthonormalBasis ℝ E i))
      x := fun j _ => (FunctionalInequalities.Analysis.BakryEmery.differentiable_fderiv_apply hf2 _ x).mul
        ((FunctionalInequalities.Analysis.BakryEmery.contDiff_fderiv_apply (FunctionalInequalities.Analysis.BakryEmery.contDiff_fderiv_apply hf (m := 2) (by norm_num) _) (m := 1)
          (by norm_num) _).differentiable one_ne_zero x)
  have hs : DifferentiableAt ℝ (fun y => ∑ j, fderiv ℝ f y (stdOrthonormalBasis ℝ E j) *
      fderiv ℝ (fun z => fderiv ℝ f z (stdOrthonormalBasis ℝ E j)) y (stdOrthonormalBasis ℝ E i))
      x := DifferentiableAt.fun_sum hd
  rw [h1, FunctionalInequalities.Analysis.BakryEmery.fderiv_const_mul_apply hs, FunctionalInequalities.Analysis.BakryEmery.fderiv_sum_apply _ hd]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [FunctionalInequalities.Analysis.BakryEmery.fderiv_mul_apply (FunctionalInequalities.Analysis.BakryEmery.differentiable_fderiv_apply hf2 _ x)
    ((FunctionalInequalities.Analysis.BakryEmery.contDiff_fderiv_apply (FunctionalInequalities.Analysis.BakryEmery.contDiff_fderiv_apply hf (m := 2) (by norm_num) _) (m := 1)
      (by norm_num) _).differentiable one_ne_zero x),
    FunctionalInequalities.Analysis.BakryEmery.bilinearIteratedFDerivTwo_eq_fderiv_apply hf2]
  ring
