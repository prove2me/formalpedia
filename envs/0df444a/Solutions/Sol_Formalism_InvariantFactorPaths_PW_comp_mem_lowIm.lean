-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.PW.comp_mem_lowIm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:46:21.238618+00:00
-- url     : https://prove2.me/submissions/a0658f09-8b3b-44ed-8ff2-ef67bf2370da

import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_OrthogonalIsomorphismHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_CommProjectionHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_CompEqZeroOfNotDle
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_gSall_le_iSup
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_GlW_Lw_le
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_GlW_comp_of_isWt
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_GlW_gS_le_Lw


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
theorem _root_.solution {μ ν : Fin n → ℤ} (hne : μ ≠ ν) {x : V} (hx : x ∈ G.gS {v | G.IsHW ν v}) :
    G.comp μ x ∈ lowIm G := by
  have hle : G.gS {v | G.IsHW ν v} ≤ (lowIm G).comap (G.comp μ) := by
    refine (gSall_le_iSup G ν).trans (iSup_le fun v => ?_)
    refine (G.gS_le_Lw v.2).trans (G.Lw_le v.1 ?_ ?_)
    · rw [Submodule.mem_comap, G.comp_of_isWt v.2.1, if_neg hne]
      exact Submodule.zero_mem _
    · intro a b hab y _
      rw [Submodule.mem_comap, G.shift]
      exact (le_iSup_of_le a (le_iSup_of_le b (le_iSup_of_le hab le_rfl)) :
        Submodule.map (G.E a b) ⊤ ≤ lowIm G) (Submodule.mem_map_of_mem Submodule.mem_top)
  exact hle hx
end Formalism.InvariantFactorPaths.PW
