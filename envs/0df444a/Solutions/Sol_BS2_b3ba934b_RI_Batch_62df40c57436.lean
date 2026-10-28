-- Prove2me | solution 1 for BS2_b3ba934b_RI_Batch_62df40c57436
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T19:19:02.519586+00:00
-- url     : https://prove2.me/submissions/be9207f6-c550-4f5c-a5df-5746ed681462

import Definitions.Def_BS2_b3ba934b_Endpoint40RecordTreeData
import Definitions.Def_BS2_b3ba934b_RecordChunking
import Definitions.Def_BS2_b3ba934b_Endpoint40RecordChecks016
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
open ThreeBoundEndpoint40Records ThreeBoundRecordLookup
attribute [local irreducible] ThreeBoundRecordLookup.checkCasesFrom ThreeBoundRecordLookup.checkCasesChunk ThreeBoundRecordLookup.checkTypes ThreeBoundRecordLookup.checkLength ThreeBoundEndpoint40Records.tree

theorem solution : (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [0,1,5,5,5]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [0,2,2,5,5]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [0,2,4,5,5]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [0,2,5,5,5]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [0,2,5,5,7]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [0,3,5,5,5]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [0,4,4,5,5]=true) ∧ True := by
  exact ⟨ThreeBoundEndpoint40Records.checked_type5_0, ThreeBoundEndpoint40Records.checked_type5_1, ThreeBoundEndpoint40Records.checked_type5_2, ThreeBoundEndpoint40Records.checked_type5_3, ThreeBoundEndpoint40Records.checked_type5_4, ThreeBoundEndpoint40Records.checked_type5_5, ThreeBoundEndpoint40Records.checked_type5_6, True.intro⟩
