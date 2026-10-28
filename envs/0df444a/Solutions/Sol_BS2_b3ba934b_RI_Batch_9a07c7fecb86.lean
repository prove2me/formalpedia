-- Prove2me | solution 1 for BS2_b3ba934b_RI_Batch_9a07c7fecb86
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T19:10:16.167+00:00
-- url     : https://prove2.me/submissions/7f985dbf-45c6-4d7a-b930-c25102cac9a1

import Definitions.Def_BS2_b3ba934b_Endpoint40RecordTreeData
import Definitions.Def_BS2_b3ba934b_RecordChunking
import Definitions.Def_BS2_b3ba934b_Endpoint40RecordSmall
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
open ThreeBoundEndpoint40Records ThreeBoundRecordLookup
attribute [local irreducible] ThreeBoundRecordLookup.checkCasesFrom ThreeBoundRecordLookup.checkCasesChunk ThreeBoundRecordLookup.checkTypes ThreeBoundRecordLookup.checkLength ThreeBoundEndpoint40Records.tree

theorem solution : (ThreeBoundRecordLookup.checkLength ThreeBoundEndpoint40Records.tree 0=true) ∧ (ThreeBoundRecordLookup.checkLength ThreeBoundEndpoint40Records.tree 1=true) ∧ (ThreeBoundRecordLookup.checkLength ThreeBoundEndpoint40Records.tree 2=true) ∧ (ThreeBoundRecordLookup.checkLength ThreeBoundEndpoint40Records.tree 3=true) ∧ True := by
  exact ⟨ThreeBoundEndpoint40Records.checked_length0, ThreeBoundEndpoint40Records.checked_length1, ThreeBoundEndpoint40Records.checked_length2, ThreeBoundEndpoint40Records.checked_length3, True.intro⟩
