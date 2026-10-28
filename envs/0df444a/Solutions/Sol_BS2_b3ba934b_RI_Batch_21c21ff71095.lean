-- Prove2me | solution 1 for BS2_b3ba934b_RI_Batch_21c21ff71095
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T19:32:18.607341+00:00
-- url     : https://prove2.me/submissions/c27a916c-11c2-4bde-991c-619f6bf3e457

import Definitions.Def_BS2_b3ba934b_Endpoint40RecordTreeData
import Definitions.Def_BS2_b3ba934b_RecordChunking
import Definitions.Def_BS2_b3ba934b_Endpoint40RecordChecks034
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
open ThreeBoundEndpoint40Records ThreeBoundRecordLookup
attribute [local irreducible] ThreeBoundRecordLookup.checkCasesFrom ThreeBoundRecordLookup.checkCasesChunk ThreeBoundRecordLookup.checkTypes ThreeBoundRecordLookup.checkLength ThreeBoundEndpoint40Records.tree

theorem solution : (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [4,5,5,6,7]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [4,5,6,7,7]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [4,7,7,7,7]=true) ∧ True := by
  exact ⟨ThreeBoundEndpoint40Records.checked_type5_136, ThreeBoundEndpoint40Records.checked_type5_138, ThreeBoundEndpoint40Records.checked_type5_140, True.intro⟩
