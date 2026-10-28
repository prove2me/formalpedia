-- Prove2me | solution 1 for BS2_b3ba934b_RI_Batch_8e2ebec860a5
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T19:40:17.686316+00:00
-- url     : https://prove2.me/submissions/9fa88d41-5246-40a8-b8e2-0b76a0f862c1

import Definitions.Def_BS2_b3ba934b_Endpoint40RecordTreeData
import Definitions.Def_BS2_b3ba934b_RecordChunking
import Definitions.Def_BS2_b3ba934b_Endpoint40RecordAssemble08
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
open ThreeBoundEndpoint40Records ThreeBoundRecordLookup
attribute [local irreducible] ThreeBoundRecordLookup.checkCasesFrom ThreeBoundRecordLookup.checkCasesChunk ThreeBoundRecordLookup.checkTypes ThreeBoundRecordLookup.checkLength ThreeBoundEndpoint40Records.tree

theorem solution : (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [3,5,5,5,5,5]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [3,5,5,5,5,7]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [4,4,4,5,5,5]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [4,4,5,5,5,5]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [4,4,5,5,5,7]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [4,5,5,5,5,5]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [4,5,5,5,5,6]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [4,5,5,5,5,7]=true) ∧ True := by
  exact ⟨ThreeBoundEndpoint40Records.checked_type6_18, ThreeBoundEndpoint40Records.checked_type6_19, ThreeBoundEndpoint40Records.checked_type6_20, ThreeBoundEndpoint40Records.checked_type6_21, ThreeBoundEndpoint40Records.checked_type6_22, ThreeBoundEndpoint40Records.checked_type6_23, ThreeBoundEndpoint40Records.checked_type6_24, ThreeBoundEndpoint40Records.checked_type6_25, True.intro⟩
