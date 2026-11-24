-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.gen_mem_supp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:10:13.350039+00:00
-- url     : https://prove2.me/submissions/80fb5cf0-801d-48d4-b20d-dd0c5cc21bea

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_StatementE
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ExistsSuppOfEvalNe
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_conjAct_map
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_conj_mem_supp
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_genMat_mul_inv
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_genMat_inv_mul

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
variable {ι ζ : Type*} {n : ℕ}
variable (k : Type*) [Field k]
variable {k}
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases
theorem _root_.solution (isVec : ι → Bool) (S : Set ι) [DecidablePred (· ∈ S)] (last : Bool)
    (G : MvPolynomial (LVar ι ζ n) k) (j : ℤ) :
    j ∈ (genAct k isVec S last G).coeff.support ↔ ∃ e ∈ (genH isVec S G).support, wExp isVec S last e = j := by
  rw [genAct, conjAct_map]
  exact conj_mem_supp isVec S (genMat_mul_inv k n) (genMat_inv_mul k n) last _ j
end Formalism.InvariantFactorPaths.GelfandTsetlinBases
