-- Prove2me | solution 1 for BS2_b3ba934b_RI_Batch_65ca5c1e3af6
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T19:39:33.741373+00:00
-- url     : https://prove2.me/submissions/cb61b3bd-ae1a-4714-b9ac-591c6fc2bb05

import Definitions.Def_BS2_b3ba934b_Endpoint40RecordTreeData
import Definitions.Def_BS2_b3ba934b_RecordChunking
import Definitions.Def_BS2_b3ba934b_Endpoint40RecordChecks056
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
open ThreeBoundEndpoint40Records ThreeBoundRecordLookup
attribute [local irreducible] ThreeBoundRecordLookup.checkCasesFrom ThreeBoundRecordLookup.checkCasesChunk ThreeBoundRecordLookup.checkTypes ThreeBoundRecordLookup.checkLength ThreeBoundEndpoint40Records.tree

theorem solution : (ThreeBoundRecordLookup.checkCasesChunk ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 2304 64=true) ∧ (ThreeBoundRecordLookup.checkCasesChunk ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 2368 64=true) ∧ (ThreeBoundRecordLookup.checkCasesChunk ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 2432 64=true) ∧ (ThreeBoundRecordLookup.checkCasesChunk ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 2496 64=true) ∧ (ThreeBoundRecordLookup.checkCasesChunk ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 2560 64=true) ∧ (ThreeBoundRecordLookup.checkCasesChunk ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 2624 64=true) ∧ (ThreeBoundRecordLookup.checkCasesChunk ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 2688 64=true) ∧ (ThreeBoundRecordLookup.checkCasesChunk ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 2752 64=true) ∧ (ThreeBoundRecordLookup.checkCasesChunk ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 2816 64=true) ∧ (ThreeBoundRecordLookup.checkCasesChunk ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 2880 64=true) ∧ (ThreeBoundRecordLookup.checkCasesChunk ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 2944 64=true) ∧ (ThreeBoundRecordLookup.checkCasesChunk ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 3008 64=true) ∧ True := by
  exact ⟨ThreeBoundEndpoint40Records.checked_type6_27_chunk2304, ThreeBoundEndpoint40Records.checked_type6_27_chunk2368, ThreeBoundEndpoint40Records.checked_type6_27_chunk2432, ThreeBoundEndpoint40Records.checked_type6_27_chunk2496, ThreeBoundEndpoint40Records.checked_type6_27_chunk2560, ThreeBoundEndpoint40Records.checked_type6_27_chunk2624, ThreeBoundEndpoint40Records.checked_type6_27_chunk2688, ThreeBoundEndpoint40Records.checked_type6_27_chunk2752, ThreeBoundEndpoint40Records.checked_type6_27_chunk2816, ThreeBoundEndpoint40Records.checked_type6_27_chunk2880, ThreeBoundEndpoint40Records.checked_type6_27_chunk2944, ThreeBoundEndpoint40Records.checked_type6_27_chunk3008, True.intro⟩
