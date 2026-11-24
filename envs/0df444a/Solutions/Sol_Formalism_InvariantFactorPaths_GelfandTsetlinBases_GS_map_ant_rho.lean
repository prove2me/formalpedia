-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.GS.map_ant_rho
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T09:41:28.167865+00:00
-- url     : https://prove2.me/submissions/dad0fafa-6f56-487f-8446-9ec60b00d61d

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_GenSpaceFacts
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ExistsSuppOfEvalNe
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_GenSpace
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_GS_act_eq

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
theorem _root_.solution (G : MvPolynomial (LVar ι ζ n) k) :
    map (ant k n : UR k n →+* UR k n) (rho isVec S G) =
      sharpHom isVec S (uMat k n)⁻¹ (uMat k n) (map (algebraMap k (UR k n)) G) := by
  rw [ant, ← act_eq, Matrix.nonsing_inv_nonsing_inv _ (uMat_det k n)]
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.GS
