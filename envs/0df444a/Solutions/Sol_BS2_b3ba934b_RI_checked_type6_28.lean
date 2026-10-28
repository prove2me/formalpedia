-- Prove2me | solution 1 for BS2_b3ba934b_RI_checked_type6_28
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T19:47:41.331554+00:00
-- url     : https://prove2.me/submissions/9d8e347a-d436-4774-b678-b238807d5494

import Definitions.Def_BS2_b3ba934b_Endpoint40RecordTreeData
import Definitions.Def_BS2_b3ba934b_RecordChunking
import Theorems.Thm_BS2_b3ba934b_RI_Batch_c0d235b91e7d
import Theorems.Thm_BS2_b3ba934b_RI_checked_type6_28_assembly_end
import Theorems.Thm_BS2_b3ba934b_RI_checked_type6_28_chunk0
import Theorems.Thm_BS2_b3ba934b_RI_checked_type6_28_chunk128
import Theorems.Thm_BS2_b3ba934b_RI_checked_type6_28_chunk64
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
open ThreeBoundEndpoint40Records ThreeBoundRecordLookup
attribute [local irreducible] ThreeBoundRecordLookup.checkCasesFrom ThreeBoundRecordLookup.checkCasesChunk ThreeBoundRecordLookup.checkTypes ThreeBoundRecordLookup.checkLength ThreeBoundEndpoint40Records.tree

theorem solution : ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [5,5,5,5,5,6]=true := by
  have ri_inline_checked_type6_28_assembly_from192 : ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,6] 192=true := by
    have h384 : ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,6] 384=true :=
      ThreeBoundRecordLookup.checkCasesFrom_step ThreeBoundEndpoint40Records.tree [5,5,5,5,5,6] 384 40 (BS2_b3ba934b_RI_Batch_c0d235b91e7d.2.2.2.1)
        (Eq.mpr
          (congrArg (fun n : Nat => ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,6] n = true)
            (show (384 + 40 : Nat) = 424 from rfl))
          BS2_b3ba934b_RI_checked_type6_28_assembly_end)
    have h320 : ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,6] 320=true :=
      ThreeBoundRecordLookup.checkCasesFrom_step ThreeBoundEndpoint40Records.tree [5,5,5,5,5,6] 320 64 (BS2_b3ba934b_RI_Batch_c0d235b91e7d.2.2.1)
        (Eq.mpr
          (congrArg (fun n : Nat => ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,6] n = true)
            (show (320 + 64 : Nat) = 384 from rfl))
          h384)
    have h256 : ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,6] 256=true :=
      ThreeBoundRecordLookup.checkCasesFrom_step ThreeBoundEndpoint40Records.tree [5,5,5,5,5,6] 256 64 (BS2_b3ba934b_RI_Batch_c0d235b91e7d.2.1)
        (Eq.mpr
          (congrArg (fun n : Nat => ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,6] n = true)
            (show (256 + 64 : Nat) = 320 from rfl))
          h320)
    have h192 : ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,6] 192=true :=
      ThreeBoundRecordLookup.checkCasesFrom_step ThreeBoundEndpoint40Records.tree [5,5,5,5,5,6] 192 64 (BS2_b3ba934b_RI_Batch_c0d235b91e7d.1)
        (Eq.mpr
          (congrArg (fun n : Nat => ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,6] n = true)
            (show (192 + 64 : Nat) = 256 from rfl))
          h256)
    exact h192
  have ri_inline_checked_type6_28_assembly_from0 : ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,6] 0=true := by
    have h128 : ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,6] 128=true :=
      ThreeBoundRecordLookup.checkCasesFrom_step ThreeBoundEndpoint40Records.tree [5,5,5,5,5,6] 128 64 BS2_b3ba934b_RI_checked_type6_28_chunk128
        (Eq.mpr
          (congrArg (fun n : Nat => ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,6] n = true)
            (show (128 + 64 : Nat) = 192 from rfl))
          ri_inline_checked_type6_28_assembly_from192)
    have h64 : ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,6] 64=true :=
      ThreeBoundRecordLookup.checkCasesFrom_step ThreeBoundEndpoint40Records.tree [5,5,5,5,5,6] 64 64 BS2_b3ba934b_RI_checked_type6_28_chunk64
        (Eq.mpr
          (congrArg (fun n : Nat => ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,6] n = true)
            (show (64 + 64 : Nat) = 128 from rfl))
          h128)
    have h0 : ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,6] 0=true :=
      ThreeBoundRecordLookup.checkCasesFrom_step ThreeBoundEndpoint40Records.tree [5,5,5,5,5,6] 0 64 BS2_b3ba934b_RI_checked_type6_28_chunk0
        (Eq.mpr
          (congrArg (fun n : Nat => ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,6] n = true)
            (show (0 + 64 : Nat) = 64 from rfl))
          h64)
    exact h0
  exact ThreeBoundRecordLookup.checkTypes_of_from ThreeBoundEndpoint40Records.tree [5,5,5,5,5,6] ri_inline_checked_type6_28_assembly_from0
