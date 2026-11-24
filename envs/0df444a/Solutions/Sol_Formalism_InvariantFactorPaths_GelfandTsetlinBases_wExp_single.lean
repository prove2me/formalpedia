-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.wExp_single
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:48:06.049164+00:00
-- url     : https://prove2.me/submissions/1cbd354e-5973-4d9a-8399-c01fbfb28f75

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
variable {ι ζ : Type*} {n : ℕ} {k : Type*} [Field k] (isVec : ι → Bool) (S : Set ι) [DecidablePred (· ∈ S)]
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases
theorem _root_.solution (last : Bool) (x : LVar ι ζ n) :
    wExp isVec S last (Finsupp.single x 1) = wtX isVec S last x := by
  simp [wExp]
end Formalism.InvariantFactorPaths.GelfandTsetlinBases
