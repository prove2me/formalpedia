-- Prove2me | solution 1 for BS2_b3ba934b_RI_Batch_8711957e6e22
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T19:39:33.690361+00:00
-- url     : https://prove2.me/submissions/98e9764b-4778-4874-b5d9-4e5e193718bd

import Definitions.Def_BS2_b3ba934b_Endpoint40RecordTreeData
import Definitions.Def_BS2_b3ba934b_RecordChunking
import Definitions.Def_BS2_b3ba934b_Endpoint40RecordChecks057
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
open ThreeBoundEndpoint40Records ThreeBoundRecordLookup
attribute [local irreducible] ThreeBoundRecordLookup.checkCasesFrom ThreeBoundRecordLookup.checkCasesChunk ThreeBoundRecordLookup.checkTypes ThreeBoundRecordLookup.checkLength ThreeBoundEndpoint40Records.tree

theorem solution : (ThreeBoundRecordLookup.checkCasesChunk ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 3072 64=true) ∧ (ThreeBoundRecordLookup.checkCasesChunk ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 3136 64=true) ∧ (ThreeBoundRecordLookup.checkCasesChunk ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 3200 64=true) ∧ (ThreeBoundRecordLookup.checkCasesChunk ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 3264 64=true) ∧ (ThreeBoundRecordLookup.checkCasesChunk ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 3328 64=true) ∧ (ThreeBoundRecordLookup.checkCasesChunk ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 3392 64=true) ∧ (ThreeBoundRecordLookup.checkCasesChunk ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 3456 64=true) ∧ (ThreeBoundRecordLookup.checkCasesChunk ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 3520 64=true) ∧ (ThreeBoundRecordLookup.checkCasesChunk ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 3584 64=true) ∧ (ThreeBoundRecordLookup.checkCasesChunk ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 3648 64=true) ∧ (ThreeBoundRecordLookup.checkCasesChunk ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 3712 64=true) ∧ (ThreeBoundRecordLookup.checkCasesChunk ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 3776 64=true) ∧ True := by
  exact ⟨ThreeBoundEndpoint40Records.checked_type6_27_chunk3072, ThreeBoundEndpoint40Records.checked_type6_27_chunk3136, ThreeBoundEndpoint40Records.checked_type6_27_chunk3200, ThreeBoundEndpoint40Records.checked_type6_27_chunk3264, ThreeBoundEndpoint40Records.checked_type6_27_chunk3328, ThreeBoundEndpoint40Records.checked_type6_27_chunk3392, ThreeBoundEndpoint40Records.checked_type6_27_chunk3456, ThreeBoundEndpoint40Records.checked_type6_27_chunk3520, ThreeBoundEndpoint40Records.checked_type6_27_chunk3584, ThreeBoundEndpoint40Records.checked_type6_27_chunk3648, ThreeBoundEndpoint40Records.checked_type6_27_chunk3712, ThreeBoundEndpoint40Records.checked_type6_27_chunk3776, True.intro⟩
