-- Prove2me | solution 1 for BS2_b3ba934b_RI_Batch_992fda005052
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T19:20:17.495557+00:00
-- url     : https://prove2.me/submissions/158768ff-a887-4875-830e-94ce3035ac55

import Definitions.Def_BS2_b3ba934b_Endpoint40RecordTreeData
import Definitions.Def_BS2_b3ba934b_RecordChunking
import Definitions.Def_BS2_b3ba934b_Endpoint40RecordChecks018
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
open ThreeBoundEndpoint40Records ThreeBoundRecordLookup
attribute [local irreducible] ThreeBoundRecordLookup.checkCasesFrom ThreeBoundRecordLookup.checkCasesChunk ThreeBoundRecordLookup.checkTypes ThreeBoundRecordLookup.checkLength ThreeBoundEndpoint40Records.tree

theorem solution : (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [1,2,2,5,5]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [1,2,2,5,7]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [1,2,3,5,5]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [1,2,4,4,5]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [1,2,4,5,5]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [1,2,4,5,7]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [1,2,5,5,6]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [1,2,5,5,7]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [1,2,5,7,7]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [1,3,4,5,5]=true) ∧ True := by
  exact ⟨ThreeBoundEndpoint40Records.checked_type5_19, ThreeBoundEndpoint40Records.checked_type5_20, ThreeBoundEndpoint40Records.checked_type5_21, ThreeBoundEndpoint40Records.checked_type5_22, ThreeBoundEndpoint40Records.checked_type5_23, ThreeBoundEndpoint40Records.checked_type5_24, ThreeBoundEndpoint40Records.checked_type5_26, ThreeBoundEndpoint40Records.checked_type5_27, ThreeBoundEndpoint40Records.checked_type5_28, ThreeBoundEndpoint40Records.checked_type5_29, True.intro⟩
