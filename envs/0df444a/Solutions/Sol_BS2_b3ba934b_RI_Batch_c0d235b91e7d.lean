-- Prove2me | solution 1 for BS2_b3ba934b_RI_Batch_c0d235b91e7d
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T19:32:28.869003+00:00
-- url     : https://prove2.me/submissions/45ec1f5a-d506-48cd-9000-b01ef7c7677e

import Definitions.Def_BS2_b3ba934b_Endpoint40RecordTreeData
import Definitions.Def_BS2_b3ba934b_RecordChunking
import Definitions.Def_BS2_b3ba934b_Endpoint40RecordChecks060
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
open ThreeBoundEndpoint40Records ThreeBoundRecordLookup
attribute [local irreducible] ThreeBoundRecordLookup.checkCasesFrom ThreeBoundRecordLookup.checkCasesChunk ThreeBoundRecordLookup.checkTypes ThreeBoundRecordLookup.checkLength ThreeBoundEndpoint40Records.tree

theorem solution : (ThreeBoundRecordLookup.checkCasesChunk ThreeBoundEndpoint40Records.tree [5,5,5,5,5,6] 192 64=true) ∧ (ThreeBoundRecordLookup.checkCasesChunk ThreeBoundEndpoint40Records.tree [5,5,5,5,5,6] 256 64=true) ∧ (ThreeBoundRecordLookup.checkCasesChunk ThreeBoundEndpoint40Records.tree [5,5,5,5,5,6] 320 64=true) ∧ (ThreeBoundRecordLookup.checkCasesChunk ThreeBoundEndpoint40Records.tree [5,5,5,5,5,6] 384 40=true) ∧ (ThreeBoundRecordLookup.checkCasesChunk ThreeBoundEndpoint40Records.tree [5,5,5,5,5,7] 0 64=true) ∧ (ThreeBoundRecordLookup.checkCasesChunk ThreeBoundEndpoint40Records.tree [5,5,5,5,5,7] 128 64=true) ∧ (ThreeBoundRecordLookup.checkCasesChunk ThreeBoundEndpoint40Records.tree [5,5,5,5,5,7] 192 64=true) ∧ (ThreeBoundRecordLookup.checkCasesChunk ThreeBoundEndpoint40Records.tree [5,5,5,5,5,7] 256 64=true) ∧ (ThreeBoundRecordLookup.checkCasesChunk ThreeBoundEndpoint40Records.tree [5,5,5,5,5,7] 320 64=true) ∧ (ThreeBoundRecordLookup.checkCasesChunk ThreeBoundEndpoint40Records.tree [5,5,5,5,5,7] 384 64=true) ∧ (ThreeBoundRecordLookup.checkCasesChunk ThreeBoundEndpoint40Records.tree [5,5,5,5,5,7] 448 64=true) ∧ (ThreeBoundRecordLookup.checkCasesChunk ThreeBoundEndpoint40Records.tree [5,5,5,5,5,7] 64 64=true) ∧ True := by
  exact ⟨ThreeBoundEndpoint40Records.checked_type6_28_chunk192, ThreeBoundEndpoint40Records.checked_type6_28_chunk256, ThreeBoundEndpoint40Records.checked_type6_28_chunk320, ThreeBoundEndpoint40Records.checked_type6_28_chunk384, ThreeBoundEndpoint40Records.checked_type6_29_chunk0, ThreeBoundEndpoint40Records.checked_type6_29_chunk128, ThreeBoundEndpoint40Records.checked_type6_29_chunk192, ThreeBoundEndpoint40Records.checked_type6_29_chunk256, ThreeBoundEndpoint40Records.checked_type6_29_chunk320, ThreeBoundEndpoint40Records.checked_type6_29_chunk384, ThreeBoundEndpoint40Records.checked_type6_29_chunk448, ThreeBoundEndpoint40Records.checked_type6_29_chunk64, True.intro⟩
