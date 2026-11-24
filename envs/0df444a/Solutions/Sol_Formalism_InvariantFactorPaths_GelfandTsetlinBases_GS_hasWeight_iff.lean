-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.GS.hasWeight_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:11:41.694913+00:00
-- url     : https://prove2.me/submissions/f0bcf3f4-7cc9-42a6-91a0-f0451c67860e

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_GenSpaceFacts
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ExistsSuppOfEvalNe
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_GenSpace
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_GS_wt_apply
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
variable {ι ζ : Type*} {n : ℕ} (isVec : ι → Bool) (S : Set ι) [DecidablePred (· ∈ S)]
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases.GS
theorem _root_.solution {k : Type*} [Field k] (f : MvPolynomial (LVar ι ζ n) k) (ν : Fin n → ℤ) :
    HasWeight isVec S f ν ↔ IsWeightedHomogeneous (wV isVec S) f ν := by
  constructor
  · intro h d hd
    funext m
    exact (wt_apply isVec S d m _ (wV_apply isVec S m)).trans (h m hd)
  · intro h m d hd
    exact (wt_apply isVec S d m _ (wV_apply isVec S m)).symm.trans (congrFun (h hd) m)
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.GS
