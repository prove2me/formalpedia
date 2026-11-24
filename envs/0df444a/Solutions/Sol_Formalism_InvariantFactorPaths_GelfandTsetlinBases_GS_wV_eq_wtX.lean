-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.GS.wV_eq_wtX
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T09:47:56.755846+00:00
-- url     : https://prove2.me/submissions/2f8724d9-3f33-4f28-8e3c-e8688f29277b

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_GenSpaceFacts
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ExistsSuppOfEvalNe
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_GenSpace
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_GS_wV_apply

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
variable {k : Type*} [Field k] {ι ζ : Type*} {n : ℕ} (isVec : ι → Bool) (S : Set ι) [DecidablePred (· ∈ S)]
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases.GS
theorem _root_.solution (last : Bool) (m : Fin n) (hm : if last then m.val + 1 = n else m.val = 0) (x : LVar ι ζ n) :
    wV isVec S x m = wtX isVec S last x := by
  rw [wV_apply]
  rcases x with ⟨i, a⟩ | z
  · have hc : (if last then a.val + 1 = n else a.val = 0) ↔ a = m := by
      cases last
      · simp only [Bool.false_eq_true, if_false] at hm ⊢
        rw [Fin.ext_iff, hm]
      · simp only [if_true] at hm ⊢
        rw [Fin.ext_iff]
        omega
    by_cases h1 : i ∈ S <;> by_cases h2 : a = m <;> simp [wtX, h1, h2, hc, hm]
  · simp [wtX]
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.GS
