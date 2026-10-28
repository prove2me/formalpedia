-- Prove2me | solution 1 for BS2_b3ba934b_RI_Batch_7d2fb1f9f947
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T19:28:22.34962+00:00
-- url     : https://prove2.me/submissions/b7246ba7-8297-4082-bc4f-fc089422a988

import Definitions.Def_BS2_b3ba934b_Endpoint40RecordTreeData
import Definitions.Def_BS2_b3ba934b_RecordChunking
import Definitions.Def_BS2_b3ba934b_Endpoint40RecordChecks028
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
open ThreeBoundEndpoint40Records ThreeBoundRecordLookup
attribute [local irreducible] ThreeBoundRecordLookup.checkCasesFrom ThreeBoundRecordLookup.checkCasesChunk ThreeBoundRecordLookup.checkTypes ThreeBoundRecordLookup.checkLength ThreeBoundEndpoint40Records.tree

theorem solution : (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [2,5,6,7,7]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [2,7,7,7,7]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [2,5,5,6,6]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [2,5,5,6,7]=true) ∧ True := by
  exact ⟨ThreeBoundEndpoint40Records.checked_type5_100, ThreeBoundEndpoint40Records.checked_type5_102, ThreeBoundEndpoint40Records.checked_type5_97, ThreeBoundEndpoint40Records.checked_type5_98, True.intro⟩
