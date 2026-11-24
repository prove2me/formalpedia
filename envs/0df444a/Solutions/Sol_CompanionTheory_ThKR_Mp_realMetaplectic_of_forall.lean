-- Prove2me | solution 1 for CompanionTheory.ThKR.Mp.realMetaplectic_of_forall
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:32:43.804798+00:00
-- url     : https://prove2.me/submissions/c2dabb34-0c1f-4579-a105-19c2497ed036

import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_LocalLift
import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_MetaplecticRepresentation_ContinuousOm
import Theorems.Thm_CompanionTheory_ThKR_Mp_om_sch
import Theorems.Thm_CompanionTheory_ThKR_Mp_om_rho
import Theorems.Thm_CompanionTheory_ThKR_Mp_continuous_om

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex SchwartzMap Matrix GlobalTheory.RealWeil CompanionTheory.ThKF.E Filter Topology CompanionTheory.ThKR.LL
open scoped Real ContDiff
namespace CompanionTheory.ThKR.Mp
theorem _root_.solution
    (h : ∀ (l : Type) [Fintype l] [DecidableEq l] [Nonempty l], Mp.TopG l ∧ Mp.Cover l ∧ Mp.Surj l ∧ Mp.Ker l ∧
      Mp.Smooth l ∧ Mp.OnePar l) : GlobalTheory.Published.RealMetaplecticRepresentation := fun l _ _ _ => by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h l
  exact ⟨Mp.G l, inferInstance, inferInstance, h1, Mp.pr, Mp.om, Mp.omS, ⟨h2, h3, h4⟩,
    Mp.continuous_om, Mp.om_rho, Mp.om_sch, h5, h6⟩
end CompanionTheory.ThKR.Mp
