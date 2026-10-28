-- Prove2me | solution 1 for BS2_b3ba934b_RI_Batch_0e8d572f7ebd
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T19:20:24.498007+00:00
-- url     : https://prove2.me/submissions/295b69ac-f02e-4920-b789-4e6f2d4ebf13

import Definitions.Def_BS2_b3ba934b_Endpoint40RecordTreeData
import Definitions.Def_BS2_b3ba934b_RecordChunking
import Definitions.Def_BS2_b3ba934b_Endpoint40RecordChecks019
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
open ThreeBoundEndpoint40Records ThreeBoundRecordLookup
attribute [local irreducible] ThreeBoundRecordLookup.checkCasesFrom ThreeBoundRecordLookup.checkCasesChunk ThreeBoundRecordLookup.checkTypes ThreeBoundRecordLookup.checkLength ThreeBoundEndpoint40Records.tree

theorem solution : (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [1,3,5,5,5]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [1,3,5,5,7]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [1,4,4,4,5]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [1,4,4,5,5]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [1,4,4,5,7]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [1,4,5,5,6]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [1,4,5,5,7]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [1,4,5,7,7]=true) ∧ True := by
  exact ⟨ThreeBoundEndpoint40Records.checked_type5_30, ThreeBoundEndpoint40Records.checked_type5_31, ThreeBoundEndpoint40Records.checked_type5_32, ThreeBoundEndpoint40Records.checked_type5_33, ThreeBoundEndpoint40Records.checked_type5_34, ThreeBoundEndpoint40Records.checked_type5_36, ThreeBoundEndpoint40Records.checked_type5_37, ThreeBoundEndpoint40Records.checked_type5_38, True.intro⟩
