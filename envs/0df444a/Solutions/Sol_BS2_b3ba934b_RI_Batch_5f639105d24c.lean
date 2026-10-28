-- Prove2me | solution 1 for BS2_b3ba934b_RI_Batch_5f639105d24c
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T19:27:43.787452+00:00
-- url     : https://prove2.me/submissions/9955bc92-0220-46df-8cb7-d85ea3011ab0

import Definitions.Def_BS2_b3ba934b_Endpoint40RecordTreeData
import Definitions.Def_BS2_b3ba934b_RecordChunking
import Definitions.Def_BS2_b3ba934b_Endpoint40RecordChecks021
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
open ThreeBoundEndpoint40Records ThreeBoundRecordLookup
attribute [local irreducible] ThreeBoundRecordLookup.checkCasesFrom ThreeBoundRecordLookup.checkCasesChunk ThreeBoundRecordLookup.checkTypes ThreeBoundRecordLookup.checkLength ThreeBoundEndpoint40Records.tree

theorem solution : (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [2,2,2,3,5]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [2,2,2,4,4]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [2,2,2,4,7]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [2,2,2,5,6]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [2,2,2,7,7]=true) ∧ True := by
  exact ⟨ThreeBoundEndpoint40Records.checked_type5_49, ThreeBoundEndpoint40Records.checked_type5_50, ThreeBoundEndpoint40Records.checked_type5_52, ThreeBoundEndpoint40Records.checked_type5_54, ThreeBoundEndpoint40Records.checked_type5_56, True.intro⟩
