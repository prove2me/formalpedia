-- Prove2me | solution 1 for CompanionTheory.ThKR.Mp.MpE.eventually_det_pos_G
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:37:54.461316+00:00
-- url     : https://prove2.me/submissions/ca04da1a-867f-4f76-838e-b375b5d75632

import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_MetaplecticRepresentation_ContinuousOm
import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_MetaplecticRepresentation_MetaplecticGroupT2Space
import Theorems.Thm_CompanionTheory_ThKR_Mp_MpE_eventually_det_pos
import Theorems.Thm_CompanionTheory_ThKR_Mp_continuous_pr


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
open CompanionTheory CompanionTheory.ThKR CompanionTheory.ThKR.Mp
variable {l : Type} [Fintype l] [DecidableEq l]
open CompanionTheory.ThKR.Mp.MpE
namespace CompanionTheory.ThKR.Mp.MpE
theorem _root_.solution : ∀ᶠ g in 𝓝 (1 : G l), 0 < (pr g).1.toBlocks₁₁.det := by
  have h := continuous_pr.tendsto (1 : G l)
  rw [map_one] at h
  exact h.eventually eventually_det_pos
end CompanionTheory.ThKR.Mp.MpE
