-- Prove2me | solution 1 for FunctionalInequalities.Analysis.BakryEmery.hessianMatrixIn_posSemidef_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:25:21.132897+00:00
-- url     : https://prove2.me/submissions/1be2ebc3-0fbb-4cf1-98ff-3d415bb96ea9

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_Calculus
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_MongeAmpere

section
noncomputable section
open InnerProductSpace
open scoped ContDiff RealInnerProductSpace
section
universe u
section DifferentialTools
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
section HessianCommutation
/-- Pointwise symmetry of the Hessian (only `C²` at the point). -/
theorem FunctionalInequalities.Analysis.BakryEmery.bilinearIteratedFDerivTwo_symm_at {f : E → ℝ} {x : E} (hf : ContDiffAt ℝ 2 f x) (u v : E) :
    bilinearIteratedFDerivTwo ℝ f x u v = bilinearIteratedFDerivTwo ℝ f x v u := by
  rw [bilinearIteratedFDerivTwo_eq_iteratedFDeriv, bilinearIteratedFDerivTwo_eq_iteratedFDeriv]
  exact (hf.isSymmSndFDerivAt (by simp)).iteratedFDeriv_cons
end HessianCommutation
end DifferentialTools
end
end
end

noncomputable section
open scoped ContDiff RealInnerProductSpace Matrix.Norms.Elementwise
open FunctionalInequalities.Analysis
open Filter Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
section Positivity
omit [FiniteDimensional ℝ E] in
/-- A nonnegative Hessian form gives a positive semidefinite Hessian matrix (pointwise `C²`). -/
theorem solution {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ E)
    {φ : E → ℝ} {x : E} (hφ : ContDiffAt ℝ 2 φ x)
    (hH : ∀ v : E, 0 ≤ bilinearIteratedFDerivTwo ℝ φ x v v) :
    (FunctionalInequalities.Analysis.BakryEmery.hessianMatrixIn φ b x).PosSemidef := by
  apply Matrix.posSemidef_iff_dotProduct_mulVec.mpr
  constructor
  · ext i j
    simp only [Matrix.conjTranspose_apply, star_trivial, FunctionalInequalities.Analysis.BakryEmery.hessianMatrixIn]
    exact FunctionalInequalities.Analysis.BakryEmery.bilinearIteratedFDerivTwo_symm_at hφ (b j) (b i)
  · intro v
    have heq : dotProduct (star v) ((FunctionalInequalities.Analysis.BakryEmery.hessianMatrixIn φ b x).mulVec v) =
        bilinearIteratedFDerivTwo ℝ φ x (∑ i, v i • b i) (∑ j, v j • b j) := by
      simp only [dotProduct, Matrix.mulVec, FunctionalInequalities.Analysis.BakryEmery.hessianMatrixIn, Pi.star_apply, star_trivial,
        map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
        smul_eq_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _hi
      apply Finset.sum_congr rfl
      intro j _hj
      rw [FunctionalInequalities.Analysis.BakryEmery.bilinearIteratedFDerivTwo_symm_at hφ (b j) (b i)]
      ring
    rw [heq]
    exact hH _
