-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.GS.genPoint_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T09:41:50.831128+00:00
-- url     : https://prove2.me/submissions/253b5acd-5608-4cd2-8610-6c2ddfef7010

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
    genPoint isVec S G =
      map (uAlg k (genMat k n) genMat_isUnit : UR k n →+* GenField k n) (rho isVec S G) :=
  act_eq isVec S (genMat k n) genMat_isUnit G
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.GS
