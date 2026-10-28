-- Prove2me | solution 1 for FunctionalInequalities.Analysis.BakryEmery.inner_gradient_gradient_inner_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:24:55.346389+00:00
-- url     : https://prove2.me/submissions/412003fe-257b-4a18-9fab-eeb84a8a8bc4

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_Calculus
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_Bochner_Basic

section
noncomputable section
open InnerProductSpace
open scoped ContDiff RealInnerProductSpace
section
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
section StdBasis
variable [FiniteDimensional ℝ E]
omit [FiniteDimensional ℝ E] in
/-- A bilinear form on two expansions `∑ aᵢ vᵢ`. -/
theorem FunctionalInequalities.Analysis.BakryEmery.bilinear_sum_smul_sum_smul {ι : Type*} [Fintype ι] (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ)
    (a : ι → ℝ) (v : ι → E) :
    B (∑ i, a i • v i) (∑ j, a j • v j) = ∑ i, ∑ j, a i * a j * B (v i) (v j) := by
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring
variable [CompleteSpace E]
/-- The gradient expanded in the standard orthonormal basis. -/
theorem FunctionalInequalities.Analysis.BakryEmery.gradient_eq_sum_fderiv_smul (f : E → ℝ) (x : E) :
    gradient f x =
      ∑ i, fderiv ℝ f x (stdOrthonormalBasis ℝ E i) • stdOrthonormalBasis ℝ E i := by
  conv_lhs => rw [← (stdOrthonormalBasis ℝ E).sum_repr' (gradient f x)]
  simp only [real_inner_comm, inner_gradient_left]
/-- A bilinear Hessian evaluated twice on a gradient, expanded in the standard basis. -/
theorem FunctionalInequalities.Analysis.BakryEmery.bilinearIteratedFDerivTwo_gradient_gradient (U f : E → ℝ) (x : E) :
    bilinearIteratedFDerivTwo ℝ U x (gradient f x) (gradient f x) =
      ∑ i, ∑ j, fderiv ℝ f x (stdOrthonormalBasis ℝ E i) * fderiv ℝ f x (stdOrthonormalBasis ℝ E j) *
        bilinearIteratedFDerivTwo ℝ U x (stdOrthonormalBasis ℝ E i) (stdOrthonormalBasis ℝ E j) := by
  rw [gradient_eq_sum_fderiv_smul]
  exact bilinear_sum_smul_sum_smul _ _ _
end StdBasis
end DifferentialTools
end
end
end

noncomputable section
open InnerProductSpace
open scoped ContDiff RealInnerProductSpace
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
section Sums
variable {ι : Type*} [Fintype ι]
theorem FunctionalInequalities.Analysis.BakryEmery.sum_mul_sum_add_swap (a u : ι → ℝ) (b w : ι → ι → ℝ) :
    ∑ j, a j * ∑ i, (u i * b i j + a i * w j i) =
      ∑ i, ∑ j, a i * a j * w i j + ∑ i, ∑ j, u i * a j * b i j := by
  simp only [Finset.mul_sum, mul_add, Finset.sum_add_distrib]
  rw [add_comm]
  congr 1
  · exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  · rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
end Sums
section Terms
variable [CompleteSpace E] [FiniteDimensional ℝ E]
/-- Drift term of `Γ(f, ℒf)`:
`⟪∇f, ∇⟪∇U, ∇f⟫⟫ = D²U(∇f, ∇f) + ∑ᵢ ∑ⱼ ∂ᵢU ∂ⱼf D²f(eᵢ, eⱼ)`, using the symmetry of `D²f`. -/
theorem solution {U f : E → ℝ} (hU : ContDiff ℝ 2 U) (hf : ContDiff ℝ 2 f)
    (x : E) :
    ⟪gradient f x, gradient (fun y => ⟪gradient U y, gradient f y⟫) x⟫ =
      bilinearIteratedFDerivTwo ℝ U x (gradient f x) (gradient f x) +
        ∑ i, ∑ j, fderiv ℝ U x (stdOrthonormalBasis ℝ E i) *
          fderiv ℝ f x (stdOrthonormalBasis ℝ E j) *
          bilinearIteratedFDerivTwo ℝ f x (stdOrthonormalBasis ℝ E i)
            (stdOrthonormalBasis ℝ E j) := by
  have h0 : (fun y => ⟪gradient U y, gradient f y⟫) = fun y =>
      ∑ i, fderiv ℝ U y (stdOrthonormalBasis ℝ E i) * fderiv ℝ f y (stdOrthonormalBasis ℝ E i) :=
    funext fun y => FunctionalInequalities.Analysis.BakryEmery.inner_gradient_eq_sum_fderiv_mul_fderiv U f y
  rw [FunctionalInequalities.Analysis.BakryEmery.inner_gradient_eq_sum_fderiv_mul_fderiv, h0, FunctionalInequalities.Analysis.BakryEmery.bilinearIteratedFDerivTwo_gradient_gradient,
    ← FunctionalInequalities.Analysis.BakryEmery.sum_mul_sum_add_swap]
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  have hd : ∀ i ∈ (Finset.univ : Finset (Fin (Module.finrank ℝ E))), DifferentiableAt ℝ
      (fun y => fderiv ℝ U y (stdOrthonormalBasis ℝ E i) * fderiv ℝ f y (stdOrthonormalBasis ℝ E i))
      x := fun i _ => (FunctionalInequalities.Analysis.BakryEmery.differentiable_fderiv_apply hU _ x).mul (FunctionalInequalities.Analysis.BakryEmery.differentiable_fderiv_apply hf _ x)
  rw [FunctionalInequalities.Analysis.BakryEmery.fderiv_sum_apply _ hd]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [FunctionalInequalities.Analysis.BakryEmery.fderiv_mul_apply (FunctionalInequalities.Analysis.BakryEmery.differentiable_fderiv_apply hU _ x) (FunctionalInequalities.Analysis.BakryEmery.differentiable_fderiv_apply hf _ x),
    ← FunctionalInequalities.Analysis.BakryEmery.bilinearIteratedFDerivTwo_eq_fderiv_apply hf, ← FunctionalInequalities.Analysis.BakryEmery.bilinearIteratedFDerivTwo_eq_fderiv_apply hU,
    FunctionalInequalities.Analysis.BakryEmery.bilinearIteratedFDerivTwo_symm hf x]
