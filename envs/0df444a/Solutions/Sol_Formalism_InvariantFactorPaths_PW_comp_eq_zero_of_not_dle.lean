-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.PW.comp_eq_zero_of_not_dle
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:46:19.8383+00:00
-- url     : https://prove2.me/submissions/897342f3-0343-4259-a60e-91d8a517a0fd

import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_OrthogonalIsomorphismHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_CommProjectionHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_CompEqZeroOfNotDle
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_gSall_le_iSup
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_GlW_wt_le_of_mem
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_wt_le_of_mem


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
variable {K V : Type} [Field K] [CharZero K] [AddCommGroup V] [Module K V] {n : ℕ} (G : GlW K V n)
namespace Formalism.InvariantFactorPaths.PW
theorem _root_.solution {μ ν : Fin n → ℤ} (hν : ¬ Dle ν μ) {x : V} (hx : x ∈ G.gS {v | G.IsHW μ v}) :
    G.comp ν x = 0 := by
  have hk : ⨆ v : {v // G.IsHW μ v}, G.gS {v.1} ≤ LinearMap.ker (G.comp ν) :=
    iSup_le fun v y hy => by
      rw [LinearMap.mem_ker]
      by_contra h
      exact hν (GlW.wt_le_of_mem G v.2 hy h)
  exact hk (gSall_le_iSup G μ hx)
end Formalism.InvariantFactorPaths.PW
