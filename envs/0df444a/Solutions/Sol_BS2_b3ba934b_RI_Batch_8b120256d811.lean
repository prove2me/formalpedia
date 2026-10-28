-- Prove2me | solution 1 for BS2_b3ba934b_RI_Batch_8b120256d811
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T19:15:04.123444+00:00
-- url     : https://prove2.me/submissions/1b3fa921-d2b1-4152-b7cd-ead7b71bc754

import Definitions.Def_BS2_b3ba934b_Endpoint40RecordTreeData
import Definitions.Def_BS2_b3ba934b_RecordChunking
import Definitions.Def_BS2_b3ba934b_Endpoint40RecordCoverage_Composition04
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
open ThreeBoundEndpoint40Records ThreeBoundRecordLookup
attribute [local irreducible] ThreeBoundRecordLookup.checkCasesFrom ThreeBoundRecordLookup.checkCasesChunk ThreeBoundRecordLookup.checkTypes ThreeBoundRecordLookup.checkLength ThreeBoundEndpoint40Records.tree

theorem solution : (ThreeBoundRecordLookup.activeTypes 6 = [
[0,5,5,5,5,5],
[1,2,5,5,5,5],
[1,4,5,5,5,5],
[1,5,5,5,5,5],
[1,5,5,5,5,7],
[2,2,2,5,5,5],
[2,2,4,5,5,5],
[2,2,5,5,5,5],
[2,2,5,5,5,7],
[2,3,5,5,5,5],
[2,4,4,5,5,5],
[2,4,5,5,5,5],
[2,4,5,5,5,7],
[2,5,5,5,5,5],
[2,5,5,5,5,6],
[2,5,5,5,5,7],
[2,5,5,5,7,7],
[3,4,5,5,5,5],
[3,5,5,5,5,5],
[3,5,5,5,5,7],
[4,4,4,5,5,5],
[4,4,5,5,5,5],
[4,4,5,5,5,7],
[4,5,5,5,5,5],
[4,5,5,5,5,6],
[4,5,5,5,5,7],
[4,5,5,5,7,7],
[5,5,5,5,5,5],
[5,5,5,5,5,6],
[5,5,5,5,5,7],
[5,5,5,5,6,7],
[5,5,5,5,7,7],
[5,5,5,7,7,7]]) ∧ True := by
  exact ⟨ThreeBoundEndpoint40Records.activeTypes6_eq, True.intro⟩
