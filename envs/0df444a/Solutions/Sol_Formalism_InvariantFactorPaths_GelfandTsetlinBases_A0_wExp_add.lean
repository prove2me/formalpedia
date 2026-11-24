-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.A0.wExp_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T09:46:39.099907+00:00
-- url     : https://prove2.me/submissions/41775b7d-0d5e-4cba-9691-91202bfbe657

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_ValuationProductsComponents
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ActFormContract
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LeIffLtColHeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_PathProductHighestWeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ExistsSuppOfEvalNe
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ValuationProductsComponents

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
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases.A0
theorem _root_.solution (last : Bool) (e e' : LVar ι ζ n →₀ ℕ) :
    wExp isVec S last (e + e') = wExp isVec S last e + wExp isVec S last e' := by
  have h : ∀ e : LVar ι ζ n →₀ ℕ,
      wExp isVec S last e = e.sum fun x d => (d : ℤ) * wtX isVec S last x := fun e => rfl
  rw [h, h, h, Finsupp.sum_add_index']
  · intro x; simp
  · intro x a b; push_cast; ring
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.A0
