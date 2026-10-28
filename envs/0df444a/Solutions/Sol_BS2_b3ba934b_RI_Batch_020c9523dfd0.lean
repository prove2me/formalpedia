-- Prove2me | solution 1 for BS2_b3ba934b_RI_Batch_020c9523dfd0
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T19:32:28.960081+00:00
-- url     : https://prove2.me/submissions/0a53a49b-936a-49b8-8c31-90679a4fef53

import Definitions.Def_BS2_b3ba934b_Endpoint40RecordTreeData
import Definitions.Def_BS2_b3ba934b_RecordChunking
import Definitions.Def_BS2_b3ba934b_Endpoint40RecordChecks061
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
open ThreeBoundEndpoint40Records ThreeBoundRecordLookup
attribute [local irreducible] ThreeBoundRecordLookup.checkCasesFrom ThreeBoundRecordLookup.checkCasesChunk ThreeBoundRecordLookup.checkTypes ThreeBoundRecordLookup.checkLength ThreeBoundEndpoint40Records.tree

theorem solution : (ThreeBoundRecordLookup.checkCasesChunk ThreeBoundEndpoint40Records.tree [5,5,5,5,5,7] 1024 64=true) ∧ (ThreeBoundRecordLookup.checkCasesChunk ThreeBoundEndpoint40Records.tree [5,5,5,5,5,7] 1088 64=true) ∧ (ThreeBoundRecordLookup.checkCasesChunk ThreeBoundEndpoint40Records.tree [5,5,5,5,5,7] 1152 64=true) ∧ (ThreeBoundRecordLookup.checkCasesChunk ThreeBoundEndpoint40Records.tree [5,5,5,5,5,7] 1216 64=true) ∧ (ThreeBoundRecordLookup.checkCasesChunk ThreeBoundEndpoint40Records.tree [5,5,5,5,5,7] 512 64=true) ∧ (ThreeBoundRecordLookup.checkCasesChunk ThreeBoundEndpoint40Records.tree [5,5,5,5,5,7] 576 64=true) ∧ (ThreeBoundRecordLookup.checkCasesChunk ThreeBoundEndpoint40Records.tree [5,5,5,5,5,7] 640 64=true) ∧ (ThreeBoundRecordLookup.checkCasesChunk ThreeBoundEndpoint40Records.tree [5,5,5,5,5,7] 704 64=true) ∧ (ThreeBoundRecordLookup.checkCasesChunk ThreeBoundEndpoint40Records.tree [5,5,5,5,5,7] 768 64=true) ∧ (ThreeBoundRecordLookup.checkCasesChunk ThreeBoundEndpoint40Records.tree [5,5,5,5,5,7] 832 64=true) ∧ (ThreeBoundRecordLookup.checkCasesChunk ThreeBoundEndpoint40Records.tree [5,5,5,5,5,7] 896 64=true) ∧ (ThreeBoundRecordLookup.checkCasesChunk ThreeBoundEndpoint40Records.tree [5,5,5,5,5,7] 960 64=true) ∧ True := by
  exact ⟨ThreeBoundEndpoint40Records.checked_type6_29_chunk1024, ThreeBoundEndpoint40Records.checked_type6_29_chunk1088, ThreeBoundEndpoint40Records.checked_type6_29_chunk1152, ThreeBoundEndpoint40Records.checked_type6_29_chunk1216, ThreeBoundEndpoint40Records.checked_type6_29_chunk512, ThreeBoundEndpoint40Records.checked_type6_29_chunk576, ThreeBoundEndpoint40Records.checked_type6_29_chunk640, ThreeBoundEndpoint40Records.checked_type6_29_chunk704, ThreeBoundEndpoint40Records.checked_type6_29_chunk768, ThreeBoundEndpoint40Records.checked_type6_29_chunk832, ThreeBoundEndpoint40Records.checked_type6_29_chunk896, ThreeBoundEndpoint40Records.checked_type6_29_chunk960, True.intro⟩
