-- Prove2me | solution 1 for Formalism.CountingSumsFrames.Har2.finrank_polAB
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:42:35.15853+00:00
-- url     : https://prove2.me/submissions/da5213a2-167e-4960-b229-844ab7ad7dd6

import Definitions.Def_Formalism_PolynomialDimension_StatementHar
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_HarmonicDecompositionHolds
import Theorems.Thm_Formalism_CountingSumsFrames_Har2_polAB_eq_restrict
import Theorems.Thm_Formalism_CountingSumsFrames_Har2_card_bideg

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
open Har2
open Formalism.CountingSumsFrames.Har2
variable {K : Type} [Field K] {k : ℕ}
namespace Formalism.CountingSumsFrames.Har2
theorem _root_.solution (k' A B : ℕ) :
    Module.finrank K (PolAB K (k' + 1) A B) = (A + k').choose k' * (B + k').choose k' := by
  rw [polAB_eq_restrict, ← card_bideg k' A B]
  exact Module.finrank_eq_nat_card_basis (MvPolynomial.basisRestrictSupport K _)
end Formalism.CountingSumsFrames.Har2
