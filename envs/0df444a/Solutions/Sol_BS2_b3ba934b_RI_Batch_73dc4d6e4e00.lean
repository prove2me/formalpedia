-- Prove2me | solution 1 for BS2_b3ba934b_RI_Batch_73dc4d6e4e00
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T19:27:48.337987+00:00
-- url     : https://prove2.me/submissions/9a97f68e-2b58-4c8e-8e4f-40fc6e248f6d

import Definitions.Def_BS2_b3ba934b_Endpoint40RecordTreeData
import Definitions.Def_BS2_b3ba934b_RecordChunking
import Definitions.Def_BS2_b3ba934b_Endpoint40RecordChecks022
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
open ThreeBoundEndpoint40Records ThreeBoundRecordLookup
attribute [local irreducible] ThreeBoundRecordLookup.checkCasesFrom ThreeBoundRecordLookup.checkCasesChunk ThreeBoundRecordLookup.checkTypes ThreeBoundRecordLookup.checkLength ThreeBoundEndpoint40Records.tree

theorem solution : (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [2,2,3,4,5]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [2,2,3,5,5]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [2,2,3,5,7]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [2,2,4,4,4]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [2,2,4,4,7]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [2,2,4,5,6]=true) ∧ True := by
  exact ⟨ThreeBoundEndpoint40Records.checked_type5_57, ThreeBoundEndpoint40Records.checked_type5_58, ThreeBoundEndpoint40Records.checked_type5_59, ThreeBoundEndpoint40Records.checked_type5_60, ThreeBoundEndpoint40Records.checked_type5_62, ThreeBoundEndpoint40Records.checked_type5_64, True.intro⟩
