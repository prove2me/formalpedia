-- Prove2me | solution 1 for BS2_b3ba934b_RI_Batch_e194d2a877ec
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T19:39:33.744977+00:00
-- url     : https://prove2.me/submissions/b3c42a93-d5b5-447b-8fea-f87424ec54d4

import Definitions.Def_BS2_b3ba934b_Endpoint40RecordTreeData
import Definitions.Def_BS2_b3ba934b_RecordChunking
import Definitions.Def_BS2_b3ba934b_Endpoint40RecordChecks032
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
open ThreeBoundEndpoint40Records ThreeBoundRecordLookup
attribute [local irreducible] ThreeBoundRecordLookup.checkCasesFrom ThreeBoundRecordLookup.checkCasesChunk ThreeBoundRecordLookup.checkTypes ThreeBoundRecordLookup.checkLength ThreeBoundEndpoint40Records.tree

theorem solution : (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [4,4,5,5,6]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [4,4,5,6,7]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [4,4,7,7,7]=true) ∧ True := by
  exact ⟨ThreeBoundEndpoint40Records.checked_type5_127, ThreeBoundEndpoint40Records.checked_type5_129, ThreeBoundEndpoint40Records.checked_type5_131, True.intro⟩
