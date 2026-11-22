-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.glAct_X
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:26:39.014073+00:00
-- url     : https://prove2.me/submissions/c522b015-12c8-4d36-bb39-867e96caf13e

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementB
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PartnerM
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_MulEarlyLettersHolds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.L4
open Formalism.GM.M MvPolynomial Finset Formalism.CountingSumsFrames
variable (p : ℕ) [Fact p.Prime] {N r : ℕ}
namespace Formalism.InvariantFactorPaths.L4
theorem _root_.solution (LL : Letters N) (j : ℕ) (a b c : Fin r) (i : Fin N) :
    glAct p LL j a b (X (i, c)) =
      if (i : ℕ) < j then (if LL.vec i then (if b = c then X (i, a) else 0) else (if a = c then -X (i, b) else 0))
      else 0 := by
  classical
  simp only [glAct, LinearMap.sum_apply]
  rw [Finset.sum_eq_single i]
  · by_cases hi : (i : ℕ) < j
    · cases hv : LL.vec i
      · by_cases hac : a = c
        · subst hac; simp [hi, hv, pderiv_X]
        · simp [hi, hv, pderiv_X, Pi.single_apply, hac, Ne.symm hac]
      · by_cases hbc : b = c
        · subst hbc; simp [hi, hv, pderiv_X]
        · simp [hi, hv, pderiv_X, Pi.single_apply, hbc, Ne.symm hbc]
    · simp [hi]
  · intro k _ hk
    split_ifs <;> simp [pderiv_X, Pi.single_apply, Ne.symm hk, hk]
  · simp
end Formalism.InvariantFactorPaths.L4
