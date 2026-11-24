-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.GS.whc_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:32:03.977045+00:00
-- url     : https://prove2.me/submissions/ca2852f8-b76f-47d5-ad87-4f03e0cf1b72

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_GenSpaceFacts
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ExistsSuppOfEvalNe
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_GenSpace
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_GS_slc_comp
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_GS_mem_genSpace
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_GS_whc_slc
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_GS_whc_rho

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
theorem _root_.solution {G f : MvPolynomial (LVar ι ζ n) k} (hf : f ∈ genSpace isVec S G) (ν : Fin n → ℤ) :
    weightedHomogeneousComponent (wV isVec S) ν f ∈ genSpace isVec S G := by
  obtain ⟨ℓ, rfl⟩ := (mem_genSpace isVec S).mp hf
  rw [whc_slc, whc_rho, slc_comp]
  exact (mem_genSpace isVec S).mpr ⟨_, rfl⟩
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.GS
