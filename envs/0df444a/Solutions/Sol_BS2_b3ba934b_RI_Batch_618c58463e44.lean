-- Prove2me | solution 1 for BS2_b3ba934b_RI_Batch_618c58463e44
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T19:32:23.707786+00:00
-- url     : https://prove2.me/submissions/64689d35-2509-4be6-ba65-03101bf4d743

import Definitions.Def_BS2_b3ba934b_Endpoint40RecordTreeData
import Definitions.Def_BS2_b3ba934b_RecordChunking
import Definitions.Def_BS2_b3ba934b_Endpoint40RecordChecks037
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
open ThreeBoundEndpoint40Records ThreeBoundRecordLookup
attribute [local irreducible] ThreeBoundRecordLookup.checkCasesFrom ThreeBoundRecordLookup.checkCasesChunk ThreeBoundRecordLookup.checkTypes ThreeBoundRecordLookup.checkLength ThreeBoundEndpoint40Records.tree

theorem solution : (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [5,5,6,6,7]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [5,5,6,7,7]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [5,6,7,7,7]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [7,7,7,7,7]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [0,5,5,5,5,5]=true) ∧ True := by
  exact ⟨ThreeBoundEndpoint40Records.checked_type5_147, ThreeBoundEndpoint40Records.checked_type5_148, ThreeBoundEndpoint40Records.checked_type5_150, ThreeBoundEndpoint40Records.checked_type5_152, ThreeBoundEndpoint40Records.checked_type6_0, True.intro⟩
