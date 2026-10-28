-- Prove2me | solution 1 for BS2_b3ba934b_RI_Batch_914c0258c256
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T19:15:08.207964+00:00
-- url     : https://prove2.me/submissions/db3ab57c-b0d5-4800-9bcd-9283f4f4277e

import Definitions.Def_BS2_b3ba934b_Endpoint40RecordTreeData
import Definitions.Def_BS2_b3ba934b_RecordChunking
import Definitions.Def_BS2_b3ba934b_Endpoint40RecordChecks037
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
open ThreeBoundEndpoint40Records ThreeBoundRecordLookup
attribute [local irreducible] ThreeBoundRecordLookup.checkCasesFrom ThreeBoundRecordLookup.checkCasesChunk ThreeBoundRecordLookup.checkTypes ThreeBoundRecordLookup.checkLength ThreeBoundEndpoint40Records.tree

theorem solution : (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [0,5,5,5,5,5]=true) ∧ True := by
  exact ⟨ThreeBoundEndpoint40Records.checked_type6_0, True.intro⟩
