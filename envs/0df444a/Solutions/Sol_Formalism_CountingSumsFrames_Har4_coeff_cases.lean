-- Prove2me | solution 1 for Formalism.CountingSumsFrames.Har4.coeff_cases
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:30:12.284113+00:00
-- url     : https://prove2.me/submissions/16563f35-e07a-4655-8b5c-97172df117ca

import Definitions.Def_Formalism_PolynomialDimension_StatementHar
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_HarmonicDecompositionHolds
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_DiagLaplacianDivPowMemSqrtFockLattice
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_SqrtFockGaussLatticeComparisonHolds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset MvPolynomial
open Formalism Formalism.CountingSumsFrames
open Formalism.CountingSumsFrames.Har4
variable {K : Type} [Field K] [CharZero K] {k A B : ℕ} (R : Subring K)
namespace Formalism.CountingSumsFrames.Har4
theorem _root_.solution {f : PolXY K k} (hf : f ∈ PolAB K k A B) (m : XY k →₀ ℕ) :
    coeff m f = 0 ∨ (xDeg m = A ∧ yDeg m = B) := by
  by_cases h : coeff m f = 0
  · exact Or.inl h
  · exact Or.inr ((show ∀ m ∈ f.support, xDeg m = A ∧ yDeg m = B from hf) m
      (MvPolynomial.mem_support_iff.2 h))
end Formalism.CountingSumsFrames.Har4
