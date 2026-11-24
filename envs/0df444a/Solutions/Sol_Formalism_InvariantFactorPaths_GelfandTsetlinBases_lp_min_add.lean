-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.lp_min_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T09:48:33.363653+00:00
-- url     : https://prove2.me/submissions/aa698d5a-7537-4a10-ae6b-fe73bb5ae2b1

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_StatementE
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ExistsSuppOfEvalNe

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
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.GelfandTsetlinBases
variable {A : Type*} [CommRing A] [IsDomain A]
omit [IsDomain A]
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases
theorem _root_.solution (x y : LaurentPolynomial A) :
    min x.coeff.support.min y.coeff.support.min ≤ (x + y).coeff.support.min := by
  classical
  apply Finset.le_min
  intro c hc
  rw [AddMonoidAlgebra.coeff_add] at hc
  rcases Finset.mem_union.mp (Finsupp.support_add hc) with h | h
  · exact min_le_of_left_le (Finset.min_le h)
  · exact min_le_of_right_le (Finset.min_le h)
end Formalism.InvariantFactorPaths.GelfandTsetlinBases
