-- Prove2me | solution 1 for FunctionalInequalities.Analysis.BakryEmery.hessianMatrixIn_posSemidef_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T14:44:32.562875+00:00
-- url     : https://prove2.me/submissions/57ed0b3b-4d8e-4fda-b9e2-8e6bb3b4af49

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Calculus
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_HessianOperator
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_MongeAmpere
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Matrix_DeterminantDerivative
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Matrix_Positivity
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Operator_Coordinates
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.TaylorIntegral
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.Algebra.Group.Matrix

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
end
end

noncomputable section
open scoped ContDiff RealInnerProductSpace Matrix.Norms.Elementwise
open FunctionalInequalities.Analysis
open Filter Topology
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
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
section Positivity
namespace FunctionalInequalities.Analysis.BakryEmery
end FunctionalInequalities.Analysis.BakryEmery
open FunctionalInequalities.Analysis.BakryEmery in
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
