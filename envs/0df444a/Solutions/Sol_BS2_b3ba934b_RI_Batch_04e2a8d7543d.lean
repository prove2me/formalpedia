-- Prove2me | solution 1 for BS2_b3ba934b_RI_Batch_04e2a8d7543d
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T19:34:17.577297+00:00
-- url     : https://prove2.me/submissions/8fed23aa-b9ef-4e79-9fa0-68d9d0489346

import Definitions.Def_BS2_b3ba934b_Endpoint40RecordTreeData
import Definitions.Def_BS2_b3ba934b_RecordChunking
import Definitions.Def_BS2_b3ba934b_Endpoint40RecordChecks064
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
open ThreeBoundEndpoint40Records ThreeBoundRecordLookup
attribute [local irreducible] ThreeBoundRecordLookup.checkCasesFrom ThreeBoundRecordLookup.checkCasesChunk ThreeBoundRecordLookup.checkTypes ThreeBoundRecordLookup.checkLength ThreeBoundEndpoint40Records.tree

theorem solution : (ThreeBoundRecordLookup.checkCasesChunk ThreeBoundEndpoint40Records.tree [5,5,5,5,7,7] 512 64=true) ∧ (ThreeBoundRecordLookup.checkCasesChunk ThreeBoundEndpoint40Records.tree [5,5,5,5,7,7] 576 64=true) ∧ (ThreeBoundRecordLookup.checkCasesChunk ThreeBoundEndpoint40Records.tree [5,5,5,5,7,7] 640 48=true) ∧ (ThreeBoundRecordLookup.checkCasesChunk ThreeBoundEndpoint40Records.tree [5,5,5,7,7,7] 0 64=true) ∧ (ThreeBoundRecordLookup.checkCasesChunk ThreeBoundEndpoint40Records.tree [5,5,5,7,7,7] 128 4=true) ∧ (ThreeBoundRecordLookup.checkCasesChunk ThreeBoundEndpoint40Records.tree [5,5,5,7,7,7] 64 64=true) ∧ True := by
  exact ⟨ThreeBoundEndpoint40Records.checked_type6_31_chunk512, ThreeBoundEndpoint40Records.checked_type6_31_chunk576, ThreeBoundEndpoint40Records.checked_type6_31_chunk640, ThreeBoundEndpoint40Records.checked_type6_32_chunk0, ThreeBoundEndpoint40Records.checked_type6_32_chunk128, ThreeBoundEndpoint40Records.checked_type6_32_chunk64, True.intro⟩
