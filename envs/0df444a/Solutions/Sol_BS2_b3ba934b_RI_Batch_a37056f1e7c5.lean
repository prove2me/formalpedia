-- Prove2me | solution 1 for BS2_b3ba934b_RI_Batch_a37056f1e7c5
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T19:39:33.752046+00:00
-- url     : https://prove2.me/submissions/d754a5e1-0cf0-414c-9859-2c02dd686644

import Definitions.Def_BS2_b3ba934b_Endpoint40RecordTreeData
import Definitions.Def_BS2_b3ba934b_RecordChunking
import Definitions.Def_BS2_b3ba934b_Endpoint40RecordChecks055
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
open ThreeBoundEndpoint40Records ThreeBoundRecordLookup
attribute [local irreducible] ThreeBoundRecordLookup.checkCasesFrom ThreeBoundRecordLookup.checkCasesChunk ThreeBoundRecordLookup.checkTypes ThreeBoundRecordLookup.checkLength ThreeBoundEndpoint40Records.tree

theorem solution : (ThreeBoundRecordLookup.checkCasesChunk ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 1536 64=true) ∧ (ThreeBoundRecordLookup.checkCasesChunk ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 1600 64=true) ∧ (ThreeBoundRecordLookup.checkCasesChunk ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 1664 64=true) ∧ (ThreeBoundRecordLookup.checkCasesChunk ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 1728 64=true) ∧ (ThreeBoundRecordLookup.checkCasesChunk ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 1792 64=true) ∧ (ThreeBoundRecordLookup.checkCasesChunk ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 1856 64=true) ∧ (ThreeBoundRecordLookup.checkCasesChunk ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 1920 64=true) ∧ (ThreeBoundRecordLookup.checkCasesChunk ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 1984 64=true) ∧ (ThreeBoundRecordLookup.checkCasesChunk ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 2048 64=true) ∧ (ThreeBoundRecordLookup.checkCasesChunk ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 2112 64=true) ∧ (ThreeBoundRecordLookup.checkCasesChunk ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 2176 64=true) ∧ (ThreeBoundRecordLookup.checkCasesChunk ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 2240 64=true) ∧ True := by
  exact ⟨ThreeBoundEndpoint40Records.checked_type6_27_chunk1536, ThreeBoundEndpoint40Records.checked_type6_27_chunk1600, ThreeBoundEndpoint40Records.checked_type6_27_chunk1664, ThreeBoundEndpoint40Records.checked_type6_27_chunk1728, ThreeBoundEndpoint40Records.checked_type6_27_chunk1792, ThreeBoundEndpoint40Records.checked_type6_27_chunk1856, ThreeBoundEndpoint40Records.checked_type6_27_chunk1920, ThreeBoundEndpoint40Records.checked_type6_27_chunk1984, ThreeBoundEndpoint40Records.checked_type6_27_chunk2048, ThreeBoundEndpoint40Records.checked_type6_27_chunk2112, ThreeBoundEndpoint40Records.checked_type6_27_chunk2176, ThreeBoundEndpoint40Records.checked_type6_27_chunk2240, True.intro⟩
