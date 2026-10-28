-- Prove2me | solution 1 for BS2_b3ba934b_RI_Batch_47945636dd74
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T19:39:33.770481+00:00
-- url     : https://prove2.me/submissions/461b21c7-5e27-461a-ad92-d13824f5fc20

import Definitions.Def_BS2_b3ba934b_Endpoint40RecordTreeData
import Definitions.Def_BS2_b3ba934b_RecordChunking
import Definitions.Def_BS2_b3ba934b_Endpoint40RecordChecks054
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
open ThreeBoundEndpoint40Records ThreeBoundRecordLookup
attribute [local irreducible] ThreeBoundRecordLookup.checkCasesFrom ThreeBoundRecordLookup.checkCasesChunk ThreeBoundRecordLookup.checkTypes ThreeBoundRecordLookup.checkLength ThreeBoundEndpoint40Records.tree

theorem solution : (ThreeBoundRecordLookup.checkCasesChunk ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 1024 64=true) ∧ (ThreeBoundRecordLookup.checkCasesChunk ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 1088 64=true) ∧ (ThreeBoundRecordLookup.checkCasesChunk ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 1152 64=true) ∧ (ThreeBoundRecordLookup.checkCasesChunk ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 1216 64=true) ∧ (ThreeBoundRecordLookup.checkCasesChunk ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 1280 64=true) ∧ (ThreeBoundRecordLookup.checkCasesChunk ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 1344 64=true) ∧ (ThreeBoundRecordLookup.checkCasesChunk ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 1408 64=true) ∧ (ThreeBoundRecordLookup.checkCasesChunk ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 1472 64=true) ∧ (ThreeBoundRecordLookup.checkCasesChunk ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 768 64=true) ∧ (ThreeBoundRecordLookup.checkCasesChunk ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 832 64=true) ∧ (ThreeBoundRecordLookup.checkCasesChunk ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 896 64=true) ∧ (ThreeBoundRecordLookup.checkCasesChunk ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 960 64=true) ∧ True := by
  exact ⟨ThreeBoundEndpoint40Records.checked_type6_27_chunk1024, ThreeBoundEndpoint40Records.checked_type6_27_chunk1088, ThreeBoundEndpoint40Records.checked_type6_27_chunk1152, ThreeBoundEndpoint40Records.checked_type6_27_chunk1216, ThreeBoundEndpoint40Records.checked_type6_27_chunk1280, ThreeBoundEndpoint40Records.checked_type6_27_chunk1344, ThreeBoundEndpoint40Records.checked_type6_27_chunk1408, ThreeBoundEndpoint40Records.checked_type6_27_chunk1472, ThreeBoundEndpoint40Records.checked_type6_27_chunk768, ThreeBoundEndpoint40Records.checked_type6_27_chunk832, ThreeBoundEndpoint40Records.checked_type6_27_chunk896, ThreeBoundEndpoint40Records.checked_type6_27_chunk960, True.intro⟩
