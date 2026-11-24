-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.A0.wge_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T09:46:32.670921+00:00
-- url     : https://prove2.me/submissions/7ebae132-15da-45e9-b84d-506c71f9817b

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_ValuationProductsComponents
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ActFormContract
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LeIffLtColHeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_PathProductHighestWeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ExistsSuppOfEvalNe
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ValuationProductsComponents
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_A0_wge_C

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
open Formalism.InvariantFactorPaths.GelfandTsetlinBases.A0
variable {ι ζ : Type*} {n : ℕ} {L : Type*} [CommRing L] (isVec : ι → Bool) (S : Set ι) [DecidablePred (· ∈ S)]
variable {isVec S} {last : Bool} {s : ℤ}
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases.A0
theorem _root_.solution (z : ℤ) : WGe isVec S last s ((z : ℤ) : MvPolynomial (LVar ι ζ n) L) 0 := by
  rw [← map_intCast (C : L →+* MvPolynomial (LVar ι ζ n) L)]
  exact wge_C _
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.A0
