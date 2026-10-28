-- Prove2me | solution 1 for BS2_b3ba934b_RI_Batch_113c145a94cf
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T19:32:23.74036+00:00
-- url     : https://prove2.me/submissions/4161cdfc-12d8-413a-8e19-c1d51dd4daef

import Definitions.Def_BS2_b3ba934b_Endpoint40RecordTreeData
import Definitions.Def_BS2_b3ba934b_RecordChunking
import Definitions.Def_BS2_b3ba934b_Endpoint40RecordChecks033
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
open ThreeBoundEndpoint40Records ThreeBoundRecordLookup
attribute [local irreducible] ThreeBoundRecordLookup.checkCasesFrom ThreeBoundRecordLookup.checkCasesChunk ThreeBoundRecordLookup.checkTypes ThreeBoundRecordLookup.checkLength ThreeBoundEndpoint40Records.tree

theorem solution : (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [4,5,5,6,6]=true) ∧ True := by
  exact ⟨ThreeBoundEndpoint40Records.checked_type5_135, True.intro⟩
