-- Prove2me | solution 1 for Formalism.CountingSumsFrames.coeff_X_mul_pderiv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:38:37.964808+00:00
-- url     : https://prove2.me/submissions/63e28595-780b-4bdf-8de2-c556deaf7e2b

import Definitions.Def_Formalism_PolynomialDimension_StatementHar
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PairingAdjointLaplacianHolds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedSimpArgs false
noncomputable section
open scoped BigOperators
open Finset MvPolynomial
open Formalism Formalism.CountingSumsFrames
variable (K : Type) [Field K] (k : ℕ)
variable {K k}
namespace Formalism.CountingSumsFrames
theorem _root_.solution (v : XY k) (f : PolXY K k) (m : XY k →₀ ℕ) :
    coeff m (X v * pderiv v f) = (m v : K) * coeff m f := by
  classical
  induction f using MvPolynomial.induction_on' with
  | add p q hp hq => simp [mul_add, hp, hq]
  | monomial n a =>
    rw [X_mul_pderiv_monomial, coeff_smul, coeff_monomial]
    by_cases h : n = m
    · subst h; simp
    · simp [h]
end Formalism.CountingSumsFrames
