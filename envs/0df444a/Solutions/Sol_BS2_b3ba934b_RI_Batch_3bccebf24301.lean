-- Prove2me | solution 1 for BS2_b3ba934b_RI_Batch_3bccebf24301
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T19:10:08.438277+00:00
-- url     : https://prove2.me/submissions/a4925cc4-cf6a-42ed-9180-213b5c6d2880

import Definitions.Def_BS2_b3ba934b_Endpoint40RecordTreeData
import Definitions.Def_BS2_b3ba934b_RecordChunking
import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
import Definitions.Def_BS2_b3ba934b_Endpoint40RecordTree
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
open ThreeBoundEndpoint40Records ThreeBoundRecordLookup
attribute [local irreducible] ThreeBoundRecordLookup.checkCasesFrom ThreeBoundRecordLookup.checkCasesChunk ThreeBoundRecordLookup.checkTypes ThreeBoundRecordLookup.checkLength ThreeBoundEndpoint40Records.tree

theorem solution : (ThreeBoundEndpoint40Records.tree.elements=ThreeBoundNumeric.Endpoint40.records) ∧ True := by
  exact ⟨ThreeBoundEndpoint40Records.tree_elements, True.intro⟩
