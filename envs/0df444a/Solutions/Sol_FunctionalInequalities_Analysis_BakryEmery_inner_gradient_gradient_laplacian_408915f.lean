-- Prove2me | solution 1 for FunctionalInequalities.Analysis.BakryEmery.inner_gradient_gradient_laplacian_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T14:41:16.799811+00:00
-- url     : https://prove2.me/submissions/e13ab614-c696-4da7-a3e7-89f51d87e608

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
section Hessian
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
/-- The bilinear second Fréchet derivative of a `C²` real-valued function is symmetric. -/
theorem FunctionalInequalities.Analysis.BakryEmery.bilinearIteratedFDerivTwo_symm {f : E → ℝ} (hf : ContDiff ℝ 2 f)
    (x v w : E) :
    bilinearIteratedFDerivTwo ℝ f x v w =
      bilinearIteratedFDerivTwo ℝ f x w v := by
  rw [bilinearIteratedFDerivTwo_eq_iteratedFDeriv,
    bilinearIteratedFDerivTwo_eq_iteratedFDeriv]
  exact (hf.contDiffAt.isSymmSndFDerivAt (by simp)).iteratedFDeriv_cons
end Hessian
section DifferentialTools
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
section Directional
/-- Mixed directional derivatives of a `C²` function commute (in directional form). -/
theorem FunctionalInequalities.Analysis.BakryEmery.fderiv_apply_comm {f : E → ℝ} (hf : ContDiff ℝ 2 f) (x v w : E) :
    fderiv ℝ (fun y => fderiv ℝ f y w) x v = fderiv ℝ (fun y => fderiv ℝ f y v) x w := by
  rw [← bilinearIteratedFDerivTwo_eq_fderiv_apply hf, ← bilinearIteratedFDerivTwo_eq_fderiv_apply hf]
  exact bilinearIteratedFDerivTwo_symm hf x v w
/-- Third-order commutation for a `C³` function: `∂_w ∂_v ∂_v f = ∂_v ∂_v ∂_w f`. The first
step commutes the two outer derivatives of the `C²` function `∂_v f`; the second commutes the two
inner derivatives of `f` at every point. -/
theorem FunctionalInequalities.Analysis.BakryEmery.fderiv_fderiv_fderiv_apply_comm {f : E → ℝ} (hf : ContDiff ℝ 3 f) (x v w : E) :
    fderiv ℝ (fun y => fderiv ℝ (fun z => fderiv ℝ f z v) y v) x w =
      fderiv ℝ (fun y => fderiv ℝ (fun z => fderiv ℝ f z w) y v) x v := by
  have hg : ContDiff ℝ 2 (fun z => fderiv ℝ f z v) := contDiff_fderiv_apply hf (by norm_num) v
  have hf2 : ContDiff ℝ 2 f := hf.of_le (by norm_num)
  have h1 : fderiv ℝ (fun y => fderiv ℝ (fun z => fderiv ℝ f z v) y v) x w =
      fderiv ℝ (fun y => fderiv ℝ (fun z => fderiv ℝ f z v) y w) x v :=
    fderiv_apply_comm hg x w v
  have h2 : (fun y => fderiv ℝ (fun z => fderiv ℝ f z v) y w) =
      fun y => fderiv ℝ (fun z => fderiv ℝ f z w) y v :=
    funext fun y => fderiv_apply_comm hf2 y w v
  rw [h1, h2]
/-- Sum rule for directional derivatives. -/
theorem FunctionalInequalities.Analysis.BakryEmery.fderiv_sum_apply {ι : Type*} (s : Finset ι) {g : ι → E → ℝ} {x : E}
    (hg : ∀ i ∈ s, DifferentiableAt ℝ (g i) x) (v : E) :
    fderiv ℝ (fun y => ∑ i ∈ s, g i y) x v = ∑ i ∈ s, fderiv ℝ (g i) x v := by
  rw [fderiv_fun_sum hg]
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
omit [CompleteSpace E] in
/-- The Laplacian of a `C²` function as a function: the trace of the iterated directional
derivatives in the standard orthonormal basis. -/
theorem FunctionalInequalities.Analysis.BakryEmery.laplacian_eq_fun_sum {g : E → ℝ} (hg : ContDiff ℝ 2 g) :
    Laplacian.laplacian g = fun x =>
      ∑ i, fderiv ℝ (fun y => fderiv ℝ g y (stdOrthonormalBasis ℝ E i)) x
        (stdOrthonormalBasis ℝ E i) :=
  funext fun x => laplacian_eq_sum_fderiv_apply_fderiv_apply
    ((hg.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero x)
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
section Terms
variable [CompleteSpace E] [FiniteDimensional ℝ E]
namespace FunctionalInequalities.Analysis.BakryEmery
end FunctionalInequalities.Analysis.BakryEmery
open FunctionalInequalities.Analysis.BakryEmery in
/-- Third-order term: `⟪∇f, ∇(Δf)⟫ = ∑ⱼ ∂ⱼf ∑ᵢ ∂ᵢ∂ᵢ∂ⱼf`, after commuting `∂ⱼ∂ᵢ∂ᵢ f = ∂ᵢ∂ᵢ∂ⱼ f`. -/
theorem solution {f : E → ℝ} (hf : ContDiff ℝ 3 f) (x : E) :
    ⟪gradient f x, gradient (Laplacian.laplacian f) x⟫ =
      ∑ j, fderiv ℝ f x (stdOrthonormalBasis ℝ E j) *
        ∑ i, fderiv ℝ (fun y => fderiv ℝ (fun z => fderiv ℝ f z (stdOrthonormalBasis ℝ E j)) y
          (stdOrthonormalBasis ℝ E i)) x (stdOrthonormalBasis ℝ E i) := by
  have hf2 : ContDiff ℝ 2 f := hf.of_le (by norm_num)
  rw [FunctionalInequalities.Analysis.BakryEmery.inner_gradient_eq_sum_fderiv_mul_fderiv, FunctionalInequalities.Analysis.BakryEmery.laplacian_eq_fun_sum hf2]
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  have hd : ∀ i ∈ (Finset.univ : Finset (Fin (Module.finrank ℝ E))), DifferentiableAt ℝ
      (fun y => fderiv ℝ (fun z => fderiv ℝ f z (stdOrthonormalBasis ℝ E i)) y
        (stdOrthonormalBasis ℝ E i)) x := fun i _ =>
    (FunctionalInequalities.Analysis.BakryEmery.contDiff_fderiv_apply (FunctionalInequalities.Analysis.BakryEmery.contDiff_fderiv_apply hf (m := 2) (by norm_num) _) (m := 1)
      (by norm_num) _).differentiable one_ne_zero x
  rw [FunctionalInequalities.Analysis.BakryEmery.fderiv_sum_apply _ hd]
  exact Finset.sum_congr rfl fun i _ => FunctionalInequalities.Analysis.BakryEmery.fderiv_fderiv_fderiv_apply_comm hf x _ _
