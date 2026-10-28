-- Prove2me | solution 1 for BS2_b3ba934b_RI_Batch_70ccdec8ec3e
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T19:28:17.881388+00:00
-- url     : https://prove2.me/submissions/3e83106d-cc6e-4dc5-8cf1-7c4842dcfe89

import Definitions.Def_BS2_b3ba934b_Endpoint40RecordTreeData
import Definitions.Def_BS2_b3ba934b_RecordChunking
import Definitions.Def_BS2_b3ba934b_Endpoint40RecordAssemble03
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
open ThreeBoundEndpoint40Records ThreeBoundRecordLookup
attribute [local irreducible] ThreeBoundRecordLookup.checkCasesFrom ThreeBoundRecordLookup.checkCasesChunk ThreeBoundRecordLookup.checkTypes ThreeBoundRecordLookup.checkLength ThreeBoundEndpoint40Records.tree

theorem solution : (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [2,5,7,7,7]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [3,4,5,5,5]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [3,5,5,5,5]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [3,5,5,5,7]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [4,4,4,4,5]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [4,4,4,5,5]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [4,4,4,5,7]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [2,5,5,7,7]=true) ∧ True := by
  exact ⟨ThreeBoundEndpoint40Records.checked_type5_101, ThreeBoundEndpoint40Records.checked_type5_109, ThreeBoundEndpoint40Records.checked_type5_113, ThreeBoundEndpoint40Records.checked_type5_115, ThreeBoundEndpoint40Records.checked_type5_120, ThreeBoundEndpoint40Records.checked_type5_122, ThreeBoundEndpoint40Records.checked_type5_124, ThreeBoundEndpoint40Records.checked_type5_99, True.intro⟩
