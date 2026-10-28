-- Prove2me | solution 1 for BS2_b3ba934b_RI_checked_type6_32_assembly_from0
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T19:40:17.769363+00:00
-- url     : https://prove2.me/submissions/44e33ec1-e97c-4a9f-87cf-7d726e514575

import Definitions.Def_BS2_b3ba934b_Endpoint40RecordTreeData
import Definitions.Def_BS2_b3ba934b_RecordChunking
import Theorems.Thm_BS2_b3ba934b_RI_Batch_04e2a8d7543d
import Theorems.Thm_BS2_b3ba934b_RI_checked_type6_32_assembly_end
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
open ThreeBoundEndpoint40Records ThreeBoundRecordLookup
attribute [local irreducible] ThreeBoundRecordLookup.checkCasesFrom ThreeBoundRecordLookup.checkCasesChunk ThreeBoundRecordLookup.checkTypes ThreeBoundRecordLookup.checkLength ThreeBoundEndpoint40Records.tree

theorem solution : ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,7,7,7] 0=true := by
  have h128 : ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,7,7,7] 128=true :=
    ThreeBoundRecordLookup.checkCasesFrom_step ThreeBoundEndpoint40Records.tree [5,5,5,7,7,7] 128 4 (BS2_b3ba934b_RI_Batch_04e2a8d7543d.2.2.2.2.1)
      (Eq.mpr
        (congrArg (fun n : Nat => ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,7,7,7] n = true)
          (show (128 + 4 : Nat) = 132 from rfl))
        BS2_b3ba934b_RI_checked_type6_32_assembly_end)
  have h64 : ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,7,7,7] 64=true :=
    ThreeBoundRecordLookup.checkCasesFrom_step ThreeBoundEndpoint40Records.tree [5,5,5,7,7,7] 64 64 (BS2_b3ba934b_RI_Batch_04e2a8d7543d.2.2.2.2.2.1)
      (Eq.mpr
        (congrArg (fun n : Nat => ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,7,7,7] n = true)
          (show (64 + 64 : Nat) = 128 from rfl))
        h128)
  have h0 : ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,7,7,7] 0=true :=
    ThreeBoundRecordLookup.checkCasesFrom_step ThreeBoundEndpoint40Records.tree [5,5,5,7,7,7] 0 64 (BS2_b3ba934b_RI_Batch_04e2a8d7543d.2.2.2.1)
      (Eq.mpr
        (congrArg (fun n : Nat => ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,7,7,7] n = true)
          (show (0 + 64 : Nat) = 64 from rfl))
        h64)
  exact h0
