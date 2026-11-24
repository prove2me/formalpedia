-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.A0.wge_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:02:22.574805+00:00
-- url     : https://prove2.me/submissions/a409f380-c310-411f-8d66-3daea4358692

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_ValuationProductsComponents
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ActFormContract
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LeIffLtColHeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_PathProductHighestWeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ExistsSuppOfEvalNe
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ValuationProductsComponents
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_A0_wge_mul
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
theorem _root_.solution {κ : Type*} (t : Finset κ) (f : κ → MvPolynomial (LVar ι ζ n) L) (a : κ → ℤ)
    (h : ∀ x ∈ t, WGe isVec S last s (f x) (a x)) :
    WGe isVec S last s (∏ x ∈ t, f x) (∑ x ∈ t, a x) := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    have := wge_C (isVec := isVec) (S := S) (last := last) (s := s) (ζ := ζ) (n := n) (1 : L)
    simpa using this
  | insert x t hx ih =>
    rw [Finset.prod_insert hx, Finset.sum_insert hx]
    exact wge_mul (h x (Finset.mem_insert_self _ _)) (ih fun y hy => h y (Finset.mem_insert_of_mem hy))
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.A0
