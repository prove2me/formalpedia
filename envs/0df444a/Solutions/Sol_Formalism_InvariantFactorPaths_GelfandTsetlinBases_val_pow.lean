-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.val_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:05:19.886544+00:00
-- url     : https://prove2.me/submissions/1ed31079-789c-4cb0-a6ba-4bff5e56fe86

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_StatementE
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ExistsSuppOfEvalNe
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_val_mul
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_val_one

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
theorem _root_.solution (G : MvPolynomial (LVar ι ζ n) k) (m : ℕ) :
    valS isVec S (G ^ m) = m • valS isVec S G := by
  induction m with
  | zero => simp [val_one]
  | succ m ih => rw [pow_succ, val_mul, ih, succ_nsmul]
end Formalism.InvariantFactorPaths.GelfandTsetlinBases
