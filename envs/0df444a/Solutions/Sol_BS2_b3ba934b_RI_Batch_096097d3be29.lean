-- Prove2me | solution 1 for BS2_b3ba934b_RI_Batch_096097d3be29
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T19:21:07.179604+00:00
-- url     : https://prove2.me/submissions/8ad6e508-b728-4cc7-a189-223b66d23cc0

import Definitions.Def_BS2_b3ba934b_Endpoint40RecordTreeData
import Definitions.Def_BS2_b3ba934b_RecordChunking
import Definitions.Def_BS2_b3ba934b_Endpoint40RecordChecks020
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
open ThreeBoundEndpoint40Records ThreeBoundRecordLookup
attribute [local irreducible] ThreeBoundRecordLookup.checkCasesFrom ThreeBoundRecordLookup.checkCasesChunk ThreeBoundRecordLookup.checkTypes ThreeBoundRecordLookup.checkLength ThreeBoundEndpoint40Records.tree

theorem solution : (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [1,5,5,5,6]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [1,5,5,6,7]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [1,5,5,7,7]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [1,5,7,7,7]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [2,2,2,2,2]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [2,2,2,2,4]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [2,2,2,2,7]=true) ∧ True := by
  exact ⟨ThreeBoundEndpoint40Records.checked_type5_40, ThreeBoundEndpoint40Records.checked_type5_42, ThreeBoundEndpoint40Records.checked_type5_43, ThreeBoundEndpoint40Records.checked_type5_44, ThreeBoundEndpoint40Records.checked_type5_45, ThreeBoundEndpoint40Records.checked_type5_46, ThreeBoundEndpoint40Records.checked_type5_48, True.intro⟩
