-- Prove2me | solution 1 for BS2_b3ba934b_RI_Batch_3c7d0de610da
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T19:20:20.943292+00:00
-- url     : https://prove2.me/submissions/b690b293-8a9a-412b-afee-95c2f16b5c58

import Definitions.Def_BS2_b3ba934b_Endpoint40RecordTreeData
import Definitions.Def_BS2_b3ba934b_RecordChunking
import Definitions.Def_BS2_b3ba934b_Endpoint40RecordAssemble00
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
open ThreeBoundEndpoint40Records ThreeBoundRecordLookup
attribute [local irreducible] ThreeBoundRecordLookup.checkCasesFrom ThreeBoundRecordLookup.checkCasesChunk ThreeBoundRecordLookup.checkTypes ThreeBoundRecordLookup.checkLength ThreeBoundEndpoint40Records.tree

theorem solution : (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [1,2,5,5,5]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [1,4,5,5,5]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [1,5,5,5,5]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [1,5,5,5,7]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [2,2,2,2,5]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [2,2,2,4,5]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [2,2,2,5,5]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [2,2,2,5,7]=true) ∧ True := by
  exact ⟨ThreeBoundEndpoint40Records.checked_type5_25, ThreeBoundEndpoint40Records.checked_type5_35, ThreeBoundEndpoint40Records.checked_type5_39, ThreeBoundEndpoint40Records.checked_type5_41, ThreeBoundEndpoint40Records.checked_type5_47, ThreeBoundEndpoint40Records.checked_type5_51, ThreeBoundEndpoint40Records.checked_type5_53, ThreeBoundEndpoint40Records.checked_type5_55, True.intro⟩
