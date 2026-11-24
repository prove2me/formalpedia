-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.GS.genH_support
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:11:33.547786+00:00
-- url     : https://prove2.me/submissions/de214889-6116-4eed-8753-e3ee68b4fb29

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_GenSpaceFacts
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ExistsSuppOfEvalNe
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_GenSpace
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_GS_uAlg_gen_injective
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_GS_map_ant_ant
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_GS_genH_eq

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
theorem _root_.solution (G : MvPolynomial (LVar ι ζ n) k) (e : LVar ι ζ n →₀ ℕ) :
    e ∈ (genH isVec S G).support ↔ e ∈ (rho isVec S G).support := by
  rw [mem_support_iff, mem_support_iff, genH_eq, coeff_map, coeff_map]
  constructor
  · intro h h0
    rw [h0, map_zero, map_zero] at h
    exact h rfl
  · intro h h0
    apply h
    have h1 : (ant k n : UR k n →+* UR k n) (coeff e (rho isVec S G)) = 0 := by
      apply uAlg_gen_injective
      rw [map_zero]
      exact h0
    have h2 := congrArg (coeff e) (map_ant_ant isVec S G)
    rw [coeff_map, coeff_map, h1, map_zero] at h2
    exact h2.symm
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.GS
