-- Prove2me | solution 1 for BS2_b3ba934b_RI_Batch_491a575ecf99
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T19:19:26.447091+00:00
-- url     : https://prove2.me/submissions/f8edb136-e12b-43f7-8545-07e7e8ff2da7

import Definitions.Def_BS2_b3ba934b_Endpoint40RecordTreeData
import Definitions.Def_BS2_b3ba934b_RecordChunking
import Definitions.Def_BS2_b3ba934b_Endpoint40RecordChecks017
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
open ThreeBoundEndpoint40Records ThreeBoundRecordLookup
attribute [local irreducible] ThreeBoundRecordLookup.checkCasesFrom ThreeBoundRecordLookup.checkCasesChunk ThreeBoundRecordLookup.checkTypes ThreeBoundRecordLookup.checkLength ThreeBoundEndpoint40Records.tree

theorem solution : (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [0,5,5,5,6]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [0,5,5,5,7]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [0,5,5,7,7]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [1,1,2,5,5]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [1,1,4,5,5]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [1,1,5,5,5]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [1,1,5,5,7]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [1,2,2,2,5]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [1,2,2,4,5]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [0,4,5,5,5]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [0,4,5,5,7]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [0,5,5,5,5]=true) ∧ True := by
  exact ⟨ThreeBoundEndpoint40Records.checked_type5_10, ThreeBoundEndpoint40Records.checked_type5_11, ThreeBoundEndpoint40Records.checked_type5_12, ThreeBoundEndpoint40Records.checked_type5_13, ThreeBoundEndpoint40Records.checked_type5_14, ThreeBoundEndpoint40Records.checked_type5_15, ThreeBoundEndpoint40Records.checked_type5_16, ThreeBoundEndpoint40Records.checked_type5_17, ThreeBoundEndpoint40Records.checked_type5_18, ThreeBoundEndpoint40Records.checked_type5_7, ThreeBoundEndpoint40Records.checked_type5_8, ThreeBoundEndpoint40Records.checked_type5_9, True.intro⟩
