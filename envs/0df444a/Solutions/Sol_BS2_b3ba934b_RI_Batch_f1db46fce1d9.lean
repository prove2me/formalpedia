-- Prove2me | solution 1 for BS2_b3ba934b_RI_Batch_f1db46fce1d9
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T19:28:26.19099+00:00
-- url     : https://prove2.me/submissions/cd5c6d37-9858-46b9-8f55-1525677721fe

import Definitions.Def_BS2_b3ba934b_Endpoint40RecordTreeData
import Definitions.Def_BS2_b3ba934b_RecordChunking
import Definitions.Def_BS2_b3ba934b_Endpoint40RecordChecks029
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
open ThreeBoundEndpoint40Records ThreeBoundRecordLookup
attribute [local irreducible] ThreeBoundRecordLookup.checkCasesFrom ThreeBoundRecordLookup.checkCasesChunk ThreeBoundRecordLookup.checkTypes ThreeBoundRecordLookup.checkLength ThreeBoundEndpoint40Records.tree

theorem solution : (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [3,3,4,5,5]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [3,3,5,5,5]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [3,3,5,5,7]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [3,4,4,4,5]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [3,4,4,5,5]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [3,4,4,5,7]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [3,4,5,5,6]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [3,4,5,5,7]=true) ∧ (ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [3,4,5,7,7]=true) ∧ True := by
  exact ⟨ThreeBoundEndpoint40Records.checked_type5_103, ThreeBoundEndpoint40Records.checked_type5_104, ThreeBoundEndpoint40Records.checked_type5_105, ThreeBoundEndpoint40Records.checked_type5_106, ThreeBoundEndpoint40Records.checked_type5_107, ThreeBoundEndpoint40Records.checked_type5_108, ThreeBoundEndpoint40Records.checked_type5_110, ThreeBoundEndpoint40Records.checked_type5_111, ThreeBoundEndpoint40Records.checked_type5_112, True.intro⟩
