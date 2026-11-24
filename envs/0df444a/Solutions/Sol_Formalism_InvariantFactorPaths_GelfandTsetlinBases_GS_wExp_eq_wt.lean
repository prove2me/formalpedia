-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.GS.wExp_eq_wt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:11:45.007833+00:00
-- url     : https://prove2.me/submissions/47506e05-4756-4f1a-863e-99540f075d47

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_GenSpaceFacts
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ExistsSuppOfEvalNe
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_GenSpace
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_GS_wt_apply
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_GS_wV_eq_wtX

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
theorem _root_.solution (last : Bool) (m : Fin n) (hm : if last then m.val + 1 = n else m.val = 0)
    (e : LVar ι ζ n →₀ ℕ) : wExp isVec S last e = wt isVec S e m := by
  rw [wt_apply isVec S e m _ (wV_eq_wtX isVec S last m hm), Finsupp.weight_apply, wExp, Finsupp.sum]
  simp
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.GS
