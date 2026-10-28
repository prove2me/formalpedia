-- Prove2me | solution 1 for BS2_b3ba934b_RI_Batch_9c087f987607
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T19:27:52.417211+00:00
-- url     : https://prove2.me/submissions/a681ed87-45fb-4140-b45c-fc0e64e31144

import Definitions.Def_BS2_b3ba934b_Endpoint40RecordTreeData
import Definitions.Def_BS2_b3ba934b_RecordChunking
import Definitions.Def_BS2_b3ba934b_Endpoint40RecordAssemble01
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
open ThreeBoundEndpoint40Records ThreeBoundRecordLookup
attribute [local irreducible] ThreeBoundRecordLookup.checkCasesFrom ThreeBoundRecordLookup.checkCasesChunk ThreeBoundRecordLookup.checkTypes ThreeBoundRecordLookup.checkLength ThreeBoundEndpoint40Records.tree

theorem solution : (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [2,2,4,4,5]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [2,2,4,5,5]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [2,2,4,5,7]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [2,2,5,5,5]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [2,2,5,5,7]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [2,2,5,7,7]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [2,3,5,5,5]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [2,4,4,4,5]=true) ∧ True := by
  exact ⟨ThreeBoundEndpoint40Records.checked_type5_61, ThreeBoundEndpoint40Records.checked_type5_63, ThreeBoundEndpoint40Records.checked_type5_65, ThreeBoundEndpoint40Records.checked_type5_67, ThreeBoundEndpoint40Records.checked_type5_69, ThreeBoundEndpoint40Records.checked_type5_71, ThreeBoundEndpoint40Records.checked_type5_77, ThreeBoundEndpoint40Records.checked_type5_82, True.intro⟩
