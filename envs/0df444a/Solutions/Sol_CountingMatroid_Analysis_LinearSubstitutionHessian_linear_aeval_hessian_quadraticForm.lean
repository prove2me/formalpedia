-- Prove2me | solution 1 for CountingMatroid.Analysis.LinearSubstitutionHessian.linear_aeval_hessian_quadraticForm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T15:29:19.434618+00:00
-- url     : https://prove2.me/submissions/dca5e698-507e-42bf-bac5-f39b77c4e485

import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Theorems.Thm_CountingMatroid_Analysis_LinearSubstitutionHessian_linear_aeval_hessian

namespace CountingMatroid.Analysis.LinearSubstitutionHessian
end CountingMatroid.Analysis.LinearSubstitutionHessian
namespace CountingMatroid.Analysis.LinearPolynomialChainRule
end CountingMatroid.Analysis.LinearPolynomialChainRule
section


set_option autoImplicit false

/-!
Linear substitutions pull back the Hessian quadratic form by their transpose
on variable values. This identity holds for arbitrary rational polynomials,
including zero substitution columns and identified variables. It provides
the algebraic part of the substitution closure in the quadratic argument.
-/

namespace CountingMatroid.Analysis.LinearSubstitutionHessian

open scoped BigOperators





/-- INTERNAL: Matrix congruence is exactly linear pullback of the associated
quadratic form, including rectangular and singular substitution matrices.
TEXLINE: main.tex:326-348 -/
theorem quadraticForm_congruence {σ τ : Type} [Fintype σ] [Fintype τ]
    [DecidableEq σ] [DecidableEq τ] (H : Matrix σ σ ℝ) (A : Matrix σ τ ℝ) :
    (A.transpose * H * A).toQuadraticForm' = H.toQuadraticForm'.comp A.toLin' := by
  have hB : Matrix.toLinearMap₂' ℝ (A.transpose * H * A) =
      (Matrix.toLinearMap₂' ℝ H).compl₁₂ A.toLin' A.toLin' := by
    apply (LinearMap.toMatrix₂' ℝ).injective
    simp
  simpa only [Matrix.toQuadraticForm', LinearMap.BilinMap.toQuadraticMap_comp_same] using
    congrArg LinearMap.BilinMap.toQuadraticMap hB



end CountingMatroid.Analysis.LinearSubstitutionHessian

end
set_option autoImplicit false

/-!
Linear substitutions pull back the Hessian quadratic form by their transpose
on variable values. This identity holds for arbitrary rational polynomials,
including zero substitution columns and identified variables. It provides
the algebraic part of the substitution closure in the quadratic argument.
-/

namespace CountingMatroid.Analysis.LinearSubstitutionHessian
end CountingMatroid.Analysis.LinearSubstitutionHessian
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.LinearSubstitutionHessian

open scoped BigOperators

/-- INTERNAL: The rational polynomial Hessian, cast to the reals, pulls back
by the real linear map of variable values under substitution.
TEXLINE: main.tex:326-348 -/
theorem solution {σ τ : Type} [Fintype σ] [Fintype τ]
    [DecidableEq σ] [DecidableEq τ] (a : σ → τ → ℚ) (p : MvPolynomial σ ℚ) :
    Matrix.toQuadraticForm' (fun i j => ((MvPolynomial.constantCoeff
      (MvPolynomial.pderiv i (MvPolynomial.pderiv j
        (MvPolynomial.aeval
          (fun s => ∑ t, MvPolynomial.C (a s t) * MvPolynomial.X t) p))) : ℚ) : ℝ)) =
    (Matrix.toQuadraticForm' (fun s t => ((MvPolynomial.constantCoeff
      (MvPolynomial.pderiv s (MvPolynomial.pderiv t p)) : ℚ) : ℝ))).comp
        (Matrix.toLin' (fun s t => (a s t : ℝ))) := by
  let A : Matrix σ τ ℝ := fun s t => (a s t : ℝ)
  let H : Matrix σ σ ℝ := fun s t => ((MvPolynomial.constantCoeff
    (MvPolynomial.pderiv s (MvPolynomial.pderiv t p)) : ℚ) : ℝ)
  have hmat : ((fun i j => ((MvPolynomial.constantCoeff
      (MvPolynomial.pderiv i (MvPolynomial.pderiv j
        (MvPolynomial.aeval
          (fun s => ∑ t, MvPolynomial.C (a s t) * MvPolynomial.X t) p))) : ℚ) : ℝ)) : Matrix τ τ ℝ) =
      A.transpose * H * A := by
    ext i j
    change _ = ∑ t, (∑ s, (a s i : ℝ) *
      ((MvPolynomial.constantCoeff (MvPolynomial.pderiv s (MvPolynomial.pderiv t p)) : ℚ) : ℝ)) *
        (a t j : ℝ)
    rw [linear_aeval_hessian]
    simp only [Rat.cast_sum, Rat.cast_mul, Finset.sum_mul]
    rw [Finset.sum_comm]
  rw [hmat]
  exact quadraticForm_congruence H A
