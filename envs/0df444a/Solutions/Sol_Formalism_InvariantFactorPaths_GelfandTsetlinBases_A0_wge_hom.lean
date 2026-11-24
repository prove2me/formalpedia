-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.A0.wge_hom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T09:53:27.335412+00:00
-- url     : https://prove2.me/submissions/ee0b5c59-6491-4e17-9a80-72d020d8a8d2

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_ValuationProductsComponents
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ActFormContract
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LeIffLtColHeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_PathProductHighestWeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ExistsSuppOfEvalNe
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ValuationProductsComponents
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_A0_wExp_weight

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
theorem _root_.solution {H : MvPolynomial (LVar ι ζ n) L} {a w : ℤ}
    (h : IsWeightedHomogeneous (wtX isVec S last) H w) (ha : H ≠ 0 → a ≤ s * w) :
    WGe isVec S last s H a := by
  intro e he
  have hne : H ≠ 0 := by
    rintro rfl
    simp at he
  rw [wExp_weight, h (mem_support_iff.1 he)]
  exact ha hne
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.A0
