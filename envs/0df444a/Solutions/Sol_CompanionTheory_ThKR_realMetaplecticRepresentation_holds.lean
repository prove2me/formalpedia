-- Prove2me | solution 1 for CompanionTheory.ThKR.realMetaplecticRepresentation_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:42:22.278983+00:00
-- url     : https://prove2.me/submissions/4c516dbb-e3f2-4227-9a28-9ced7284db41

import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_MetaplecticRepresentation_ContinuousTo
import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_MetaplecticRepresentation_MetaplecticUnipotentBlockSecondDiag
import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_MetaplecticRepresentation_MapOfRealMul
import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_MetaplecticRepresentation_HasFDerivAtOfCurves
import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_MetaplecticRepresentation_MetaplecticGroupT2Space
import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_MetaplecticRepresentation_HasFDerivAtOrb
import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_MetaplecticRepresentation_RealMetaplecticRepresentationHolds
import Theorems.Thm_CompanionTheory_ThKR_Mp_cover_of
import Theorems.Thm_CompanionTheory_ThKR_Mp_ddNe
import Theorems.Thm_CompanionTheory_ThKR_Mp_ker
import Theorems.Thm_CompanionTheory_ThKR_Mp_mkElt
import Theorems.Thm_CompanionTheory_ThKR_Mp_nearOne_of
import Theorems.Thm_CompanionTheory_ThKR_Mp_nrmUp
import Theorems.Thm_CompanionTheory_ThKR_Mp_onePar_of
import Theorems.Thm_CompanionTheory_ThKR_Mp_realMetaplectic_of_forall
import Theorems.Thm_CompanionTheory_ThKR_Mp_secDer
import Theorems.Thm_CompanionTheory_ThKR_Mp_secEx_of
import Theorems.Thm_CompanionTheory_ThKR_Mp_smooth_of
import Theorems.Thm_CompanionTheory_ThKR_Mp_surj_of
import Theorems.Thm_CompanionTheory_ThKR_Mp_topG


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

open CompanionTheory.ThKR.Mp
namespace CompanionTheory.ThKR
theorem _root_.solution : GlobalTheory.Published.RealMetaplecticRepresentation :=
  realMetaplectic_of_forall fun l _ _ _ =>
    have hS : SecEx l := secEx_of mkElt nrmUp
    have hO : Surj l := surj_of ddNe hS
    have hN : NearOne l := nearOne_of hS ker secDer
    have hC : Cover l := cover_of topG hO ker hS secDer
    ⟨topG, hC, hO, ker, smooth_of topG hN secDer, onePar_of topG hC hN secDer⟩
end CompanionTheory.ThKR
