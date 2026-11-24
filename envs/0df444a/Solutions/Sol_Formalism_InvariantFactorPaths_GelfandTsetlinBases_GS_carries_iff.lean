-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.GS.carries_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:11:30.826463+00:00
-- url     : https://prove2.me/submissions/8482aa16-ea36-4bfb-ac87-8304d8ad8948

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_GenSpaceFacts
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ExistsSuppOfEvalNe
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_GenSpace
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_GS_slSpace_map
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_GS_mem_span_iff
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_GS_uAlg_gen_injective
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_GS_genPoint_eq

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
theorem _root_.solution (G : MvPolynomial (LVar ι ζ n) k) (N : Submodule k (MvPolynomial (LVar ι ζ n) k)) :
    Carries isVec S G N ↔ slSpace (k := k) (rho isVec S G) ≤ N := by
  refine (mem_span_iff (A := GenField k n) N (genPoint isVec S G)).trans ?_
  rw [genPoint_eq, slSpace_map _ uAlg_gen_injective]
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.GS
