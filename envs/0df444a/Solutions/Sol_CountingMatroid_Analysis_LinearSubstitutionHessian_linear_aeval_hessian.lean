-- Prove2me | solution 1 for CountingMatroid.Analysis.LinearSubstitutionHessian.linear_aeval_hessian
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T15:26:51.393441+00:00
-- url     : https://prove2.me/submissions/daa39390-727c-4410-9e33-eb2b1b870da6

import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Theorems.Thm_CountingMatroid_Analysis_LinearPolynomialChainRule_linear_aeval_pderiv

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

/-- INTERNAL: A linear substitution without a constant term preserves the
constant coefficient.
TEXLINE: main.tex:326-348 -/
theorem constantCoeff_linear_aeval {σ τ : Type} [Fintype τ]
    (a : σ → τ → ℚ) (p : MvPolynomial σ ℚ) :
    MvPolynomial.constantCoeff
      (MvPolynomial.aeval (fun s => ∑ t, MvPolynomial.C (a s t) * MvPolynomial.X t) p) =
    MvPolynomial.constantCoeff p := by
  induction p using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p s hp => simp [hp]







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

/-- INTERNAL: The Hessian transforms by matrix congruence under a linear
substitution; this is a coefficient identity before casting to the reals.
TEXLINE: main.tex:326-348 -/
theorem solution {σ τ : Type} [Fintype σ] [Fintype τ]
    (a : σ → τ → ℚ) (p : MvPolynomial σ ℚ) (i j : τ) :
    MvPolynomial.constantCoeff
      (MvPolynomial.pderiv i (MvPolynomial.pderiv j
        (MvPolynomial.aeval
          (fun s => ∑ t, MvPolynomial.C (a s t) * MvPolynomial.X t) p))) =
    ∑ s, ∑ t, a s i *
      MvPolynomial.constantCoeff (MvPolynomial.pderiv s (MvPolynomial.pderiv t p)) *
        a t j := by
  classical
  rw [LinearPolynomialChainRule.linear_aeval_pderiv,
    LinearPolynomialChainRule.linear_aeval_pderiv,
    constantCoeff_linear_aeval]
  simp only [map_sum, MvPolynomial.pderiv_C_mul, map_mul, MvPolynomial.constantCoeff_C]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro t _
  ring
