-- Prove2me | solution 1 for BS2_b3ba934b_RI_Batch_c073237de769
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T19:27:57.313293+00:00
-- url     : https://prove2.me/submissions/2782ec1c-8c10-4946-b997-d76435c48b0f

import Definitions.Def_BS2_b3ba934b_Endpoint40RecordTreeData
import Definitions.Def_BS2_b3ba934b_RecordChunking
import Definitions.Def_BS2_b3ba934b_Endpoint40RecordChecks023
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
open ThreeBoundEndpoint40Records ThreeBoundRecordLookup
attribute [local irreducible] ThreeBoundRecordLookup.checkCasesFrom ThreeBoundRecordLookup.checkCasesChunk ThreeBoundRecordLookup.checkTypes ThreeBoundRecordLookup.checkLength ThreeBoundEndpoint40Records.tree

theorem solution : (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [2,2,4,7,7]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [2,2,5,5,6]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [2,2,5,6,7]=true) ∧ True := by
  exact ⟨ThreeBoundEndpoint40Records.checked_type5_66, ThreeBoundEndpoint40Records.checked_type5_68, ThreeBoundEndpoint40Records.checked_type5_70, True.intro⟩
