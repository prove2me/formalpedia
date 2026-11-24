-- Prove2me | solution 1 for CompanionTheory.ThKR.Mp.MpE.sec_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:30:34.368441+00:00
-- url     : https://prove2.me/submissions/2e18fa79-8984-42e7-8ca6-29455e754d7e

import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_MetaplecticRepresentation_ContinuousOm
import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_MetaplecticRepresentation_MetaplecticGroupT2Space
import Theorems.Thm_P2M_CompanionTheory_ThKR_Mp_MpE_toBlocks___one__0a88a243d007
import Theorems.Thm_CompanionTheory_ThKR_LL_big_one
import Theorems.Thm_CompanionTheory_ThKR_LL_block_inl_inl_one
import Theorems.Thm_CompanionTheory_ThKR_LL_block_inl_inr_one
import Theorems.Thm_CompanionTheory_ThKR_LL_block_inr_inl_one


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
theorem _root_.solution : sec (1 : Mat l) = 1 := by
  rw [sec, block_inl_inl_one, block_inl_inr_one, block_inr_inl_one, toBlocks₁₁_one', Matrix.det_one, abs_one, Real.sqrt_one, inv_one,
    Ring.inverse_one, big_one]
end CompanionTheory.ThKR.Mp.MpE
