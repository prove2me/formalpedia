-- Prove2me | solution 1 for Formalism.L2.Pj.complSt_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:38:19.345001+00:00
-- url     : https://prove2.me/submissions/407e17a6-31ab-479b-9d61-5dd88405624a

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ComplSt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_CompletionDVR
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ComplPf
import Theorems.Thm_GlobalTheory_irreducible_algebraMap_adicCompletion_of_dvr


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.L2 Formalism.L2.Pj
open IsLocalRing
namespace Formalism.L2.Pj
theorem _root_.solution : ComplSt := by
  intro W _ _ _ _
  haveI : CharZero (AdicCompletion (maximalIdeal W) W) :=
    charZero_of_injective_algebraMap (GlobalTheory.algebraMap_adicCompletion_injective_of_dvr W)
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible W
  have hl : IsLocalHom (algebraMap W (AdicCompletion (maximalIdeal W) W)) := inferInstance
  exact ⟨⟨AdicCompletion (maximalIdeal W) W⟩, algebraMap W (AdicCompletion (maximalIdeal W) W), hl, ϖ, hϖ,
    GlobalTheory.irreducible_algebraMap_adicCompletion_of_dvr hϖ⟩
end Formalism.L2.Pj
