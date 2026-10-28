-- Prove2me | solution 1 for BS2_b3ba934b_RI_Batch_4bb724743bd9
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T19:10:12.32408+00:00
-- url     : https://prove2.me/submissions/de4c1cf2-d701-4135-9c8c-0258589ed719

import Definitions.Def_BS2_b3ba934b_Endpoint40RecordTreeData
import Definitions.Def_BS2_b3ba934b_RecordChunking
import Definitions.Def_BS2_b3ba934b_Endpoint40RecordCoverage_Composition01
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
open ThreeBoundEndpoint40Records ThreeBoundRecordLookup
attribute [local irreducible] ThreeBoundRecordLookup.checkCasesFrom ThreeBoundRecordLookup.checkCasesChunk ThreeBoundRecordLookup.checkTypes ThreeBoundRecordLookup.checkLength ThreeBoundEndpoint40Records.tree

theorem solution : (ThreeBoundRecordLookup.checkLength ThreeBoundEndpoint40Records.tree 4=true) ∧ True := by
  exact ⟨ThreeBoundEndpoint40Records.checked_length4, True.intro⟩
