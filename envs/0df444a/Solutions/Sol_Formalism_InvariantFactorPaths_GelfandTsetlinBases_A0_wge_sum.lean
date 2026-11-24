-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.A0.wge_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T09:55:28.951314+00:00
-- url     : https://prove2.me/submissions/90f2fde3-0d2c-48cc-a966-ea305e5b6e4b

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_ValuationProductsComponents
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ActFormContract
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LeIffLtColHeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_PathProductHighestWeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ExistsSuppOfEvalNe
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ValuationProductsComponents
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_A0_wge_zero
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_A0_wge_add

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
theorem _root_.solution {κ : Type*} (t : Finset κ) (f : κ → MvPolynomial (LVar ι ζ n) L) {a : ℤ}
    (h : ∀ x ∈ t, WGe isVec S last s (f x) a) : WGe isVec S last s (∑ x ∈ t, f x) a := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using wge_zero a
  | insert x t hx ih =>
    rw [Finset.sum_insert hx]
    exact wge_add (h x (Finset.mem_insert_self _ _)) (ih fun y hy => h y (Finset.mem_insert_of_mem hy))
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.A0
