-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.PW.comm_projection_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:21:13.012881+00:00
-- url     : https://prove2.me/submissions/61c0f067-799c-4e05-8b96-031588fa5f44

import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_WeightCompApply
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_StatementC
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_CommProjectionHolds
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_isoC_stable
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_isoC_map_of_comm
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_typeProj_comm
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_glAct_split
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_midAct_comm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.PW
open Formalism.GM.M Formalism.GM.DimensionMonotonicity MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
namespace Formalism.InvariantFactorPaths.PW
theorem _root_.solution : CommP := by
  intro p _ N r LL j j' Cs Cs' T T' P P' hj hC hP hP'
  have h1 : ∀ c ∈ Cs', ∀ d ∈ Cs', ∀ x, P (glAct p LL j' c d x) = glAct p LL j' c d (P x) := by
    intro c hc d hd x
    have := typeProj_comm LL j Cs T P hP (glAct p LL j' c d) (by
      intro la y hy
      rw [glAct_split LL hj c d, LinearMap.add_apply]
      refine Submodule.add_mem _ (isoC_stable LL j Cs la c (hC hc) d (hC hd) y hy) ?_
      exact isoC_map_of_comm LL j Cs (midAct p LL j j' c d)
        (fun c' _ d' _ z => midAct_comm LL j j' c d c' d' z) la y hy)
    exact congrArg (fun f => f x) this
  exact (typeProj_comm LL j' Cs' T' P' hP' P (isoC_map_of_comm LL j' Cs' P h1)).symm
end Formalism.InvariantFactorPaths.PW
