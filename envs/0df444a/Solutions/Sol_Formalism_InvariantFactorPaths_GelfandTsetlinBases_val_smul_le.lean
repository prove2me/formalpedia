-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.val_smul_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T09:52:32.095302+00:00
-- url     : https://prove2.me/submissions/28b298a3-800c-44b3-a0d5-3e0ba99c59f9

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_StatementE
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ExistsSuppOfEvalNe
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_val_C
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_val_mul
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_val_zero

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
theorem _root_.solution (θ : WithTop ℤ) (c : k) (G : MvPolynomial (LVar ι ζ n) k) (h : θ ≤ valS isVec S G) :
    θ ≤ valS isVec S (c • G) := by
  by_cases hc : c = 0
  · simp [hc, val_zero]
  · rw [MvPolynomial.smul_eq_C_mul, val_mul, val_C isVec S hc, zero_add]; exact h
end Formalism.InvariantFactorPaths.GelfandTsetlinBases
