-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.PW.isoC_inf_pol_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:11:43.839057+00:00
-- url     : https://prove2.me/submissions/c95325ec-a477-4fc5-97d0-02a39b056ffe

import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_LatData
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_CommProjectionHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_StatementB
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_ZpClosedToAddSubgroup
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_polProj_mem
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_polProj_id
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_polProj_glAct
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_GlW_gS_stable
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_GlW_subset_gS
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_GAe_E
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_hwc_iff
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_hwc_map_of_comm
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_stableC_iff


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
theorem _root_.solution (LL L2 : Letters N) (j : ℕ) (Cs : Finset (Fin r)) (la : Fin r → ℤ) :
    IsoC p LL j Cs la ⊓ Pol p r L2 ≤ IsoW (GAe p LL j (enumC Cs)) (Pol p r L2) (la ∘ enumC Cs) := by
  have hle : IsoC p LL j Cs la ≤
      (IsoW (GAe p LL j (enumC Cs)) (Pol p r L2) (la ∘ enumC Cs)).comap (polProj p r L2) := by
    rw [IsoC]
    refine sInf_le ⟨?_, ?_⟩
    · intro x hx
      rw [Submodule.mem_comap]
      refine (GAe p LL j (enumC Cs)).subset_gS _ ⟨?_, polProj_mem L2 x⟩
      exact (hwc_iff LL j Cs la _).mp
        (hwc_map_of_comm LL j Cs _ (fun c _ d _ y => polProj_glAct LL L2 j c d y) la x hx)
    · rw [stableC_iff]
      intro a b x hx
      rw [Submodule.mem_comap] at hx ⊢
      rw [GAe_E, polProj_glAct]
      exact (GAe p LL j (enumC Cs)).gS_stable _ a b _ hx
  intro x hx
  have h := hle hx.1
  rwa [Submodule.mem_comap, polProj_id L2 hx.2] at h
end Formalism.InvariantFactorPaths.PW
