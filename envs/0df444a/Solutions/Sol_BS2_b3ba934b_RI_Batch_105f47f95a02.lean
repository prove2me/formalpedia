-- Prove2me | solution 1 for BS2_b3ba934b_RI_Batch_105f47f95a02
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T19:39:19.504424+00:00
-- url     : https://prove2.me/submissions/94d62023-1be3-4018-8d64-e26e1bb916b7

import Definitions.Def_BS2_b3ba934b_Endpoint40RecordTreeData
import Definitions.Def_BS2_b3ba934b_RecordChunking
import Definitions.Def_BS2_b3ba934b_Endpoint40RecordChecks053
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
open ThreeBoundEndpoint40Records ThreeBoundRecordLookup
attribute [local irreducible] ThreeBoundRecordLookup.checkCasesFrom ThreeBoundRecordLookup.checkCasesChunk ThreeBoundRecordLookup.checkTypes ThreeBoundRecordLookup.checkLength ThreeBoundEndpoint40Records.tree

theorem solution : (ThreeBoundRecordLookup.checkCasesChunk ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 0 64=true) ∧ (ThreeBoundRecordLookup.checkCasesChunk ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 128 64=true) ∧ (ThreeBoundRecordLookup.checkCasesChunk ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 192 64=true) ∧ (ThreeBoundRecordLookup.checkCasesChunk ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 256 64=true) ∧ (ThreeBoundRecordLookup.checkCasesChunk ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 320 64=true) ∧ (ThreeBoundRecordLookup.checkCasesChunk ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 384 64=true) ∧ (ThreeBoundRecordLookup.checkCasesChunk ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 448 64=true) ∧ (ThreeBoundRecordLookup.checkCasesChunk ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 512 64=true) ∧ (ThreeBoundRecordLookup.checkCasesChunk ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 576 64=true) ∧ (ThreeBoundRecordLookup.checkCasesChunk ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 64 64=true) ∧ (ThreeBoundRecordLookup.checkCasesChunk ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 640 64=true) ∧ (ThreeBoundRecordLookup.checkCasesChunk ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 704 64=true) ∧ True := by
  exact ⟨ThreeBoundEndpoint40Records.checked_type6_27_chunk0, ThreeBoundEndpoint40Records.checked_type6_27_chunk128, ThreeBoundEndpoint40Records.checked_type6_27_chunk192, ThreeBoundEndpoint40Records.checked_type6_27_chunk256, ThreeBoundEndpoint40Records.checked_type6_27_chunk320, ThreeBoundEndpoint40Records.checked_type6_27_chunk384, ThreeBoundEndpoint40Records.checked_type6_27_chunk448, ThreeBoundEndpoint40Records.checked_type6_27_chunk512, ThreeBoundEndpoint40Records.checked_type6_27_chunk576, ThreeBoundEndpoint40Records.checked_type6_27_chunk64, ThreeBoundEndpoint40Records.checked_type6_27_chunk640, ThreeBoundEndpoint40Records.checked_type6_27_chunk704, True.intro⟩
