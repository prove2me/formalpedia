-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.GS.wV_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T09:41:40.054604+00:00
-- url     : https://prove2.me/submissions/58f678ea-6917-4587-aa5a-cd275304fa3c

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_GenSpaceFacts
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ExistsSuppOfEvalNe
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_GenSpace

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
open Formalism.InvariantFactorPaths.GelfandTsetlinBases.GS
variable {ι ζ : Type*} {n : ℕ} (isVec : ι → Bool) (S : Set ι) [DecidablePred (· ∈ S)]
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases.GS
theorem _root_.solution (m : Fin n) (x : LVar ι ζ n) :
    wV isVec S x m = match x with
        | Sum.inl (i, a) => if i ∈ S ∧ a = m then (if isVec i then (1 : ℤ) else -1) else 0
        | Sum.inr _ => 0 := by
  rcases x with ⟨i, a⟩ | z
  · by_cases h1 : i ∈ S
    · by_cases h2 : a = m
      · subst h2
        cases h3 : isVec i <;> simp [wV, h1, h3]
      · cases h3 : isVec i <;> simp [wV, h1, h2, h3, Ne.symm h2]
    · simp [wV, h1]
  · simp [wV]
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.GS
