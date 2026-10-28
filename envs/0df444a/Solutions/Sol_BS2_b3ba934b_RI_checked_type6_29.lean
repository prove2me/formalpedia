-- Prove2me | solution 1 for BS2_b3ba934b_RI_checked_type6_29
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T19:46:29.039281+00:00
-- url     : https://prove2.me/submissions/54258d46-a905-4352-adc2-11a29fab6a4f

import Definitions.Def_BS2_b3ba934b_Endpoint40RecordTreeData
import Definitions.Def_BS2_b3ba934b_RecordChunking
import Theorems.Thm_BS2_b3ba934b_RI_Batch_020c9523dfd0
import Theorems.Thm_BS2_b3ba934b_RI_Batch_c0d235b91e7d
import Theorems.Thm_BS2_b3ba934b_RI_checked_type6_29_assembly_from1408
import Theorems.Thm_BS2_b3ba934b_RI_checked_type6_29_chunk1280
import Theorems.Thm_BS2_b3ba934b_RI_checked_type6_29_chunk1344
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
open ThreeBoundEndpoint40Records ThreeBoundRecordLookup
attribute [local irreducible] ThreeBoundRecordLookup.checkCasesFrom ThreeBoundRecordLookup.checkCasesChunk ThreeBoundRecordLookup.checkTypes ThreeBoundRecordLookup.checkLength ThreeBoundEndpoint40Records.tree

theorem solution : ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [5,5,5,5,5,7]=true := by
  have ri_inline_checked_type6_29_assembly_from1152 : ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,7] 1152=true := by
    have h1344 : ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,7] 1344=true :=
      ThreeBoundRecordLookup.checkCasesFrom_step ThreeBoundEndpoint40Records.tree [5,5,5,5,5,7] 1344 64 BS2_b3ba934b_RI_checked_type6_29_chunk1344
        (Eq.mpr
          (congrArg (fun n : Nat => ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,7] n = true)
            (show (1344 + 64 : Nat) = 1408 from rfl))
          BS2_b3ba934b_RI_checked_type6_29_assembly_from1408)
    have h1280 : ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,7] 1280=true :=
      ThreeBoundRecordLookup.checkCasesFrom_step ThreeBoundEndpoint40Records.tree [5,5,5,5,5,7] 1280 64 BS2_b3ba934b_RI_checked_type6_29_chunk1280
        (Eq.mpr
          (congrArg (fun n : Nat => ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,7] n = true)
            (show (1280 + 64 : Nat) = 1344 from rfl))
          h1344)
    have h1216 : ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,7] 1216=true :=
      ThreeBoundRecordLookup.checkCasesFrom_step ThreeBoundEndpoint40Records.tree [5,5,5,5,5,7] 1216 64 (BS2_b3ba934b_RI_Batch_020c9523dfd0.2.2.2.1)
        (Eq.mpr
          (congrArg (fun n : Nat => ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,7] n = true)
            (show (1216 + 64 : Nat) = 1280 from rfl))
          h1280)
    have h1152 : ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,7] 1152=true :=
      ThreeBoundRecordLookup.checkCasesFrom_step ThreeBoundEndpoint40Records.tree [5,5,5,5,5,7] 1152 64 (BS2_b3ba934b_RI_Batch_020c9523dfd0.2.2.1)
        (Eq.mpr
          (congrArg (fun n : Nat => ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,7] n = true)
            (show (1152 + 64 : Nat) = 1216 from rfl))
          h1216)
    exact h1152
  have ri_inline_checked_type6_29_assembly_from896 : ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,7] 896=true := by
    have h1088 : ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,7] 1088=true :=
      ThreeBoundRecordLookup.checkCasesFrom_step ThreeBoundEndpoint40Records.tree [5,5,5,5,5,7] 1088 64 (BS2_b3ba934b_RI_Batch_020c9523dfd0.2.1)
        (Eq.mpr
          (congrArg (fun n : Nat => ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,7] n = true)
            (show (1088 + 64 : Nat) = 1152 from rfl))
          ri_inline_checked_type6_29_assembly_from1152)
    have h1024 : ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,7] 1024=true :=
      ThreeBoundRecordLookup.checkCasesFrom_step ThreeBoundEndpoint40Records.tree [5,5,5,5,5,7] 1024 64 (BS2_b3ba934b_RI_Batch_020c9523dfd0.1)
        (Eq.mpr
          (congrArg (fun n : Nat => ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,7] n = true)
            (show (1024 + 64 : Nat) = 1088 from rfl))
          h1088)
    have h960 : ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,7] 960=true :=
      ThreeBoundRecordLookup.checkCasesFrom_step ThreeBoundEndpoint40Records.tree [5,5,5,5,5,7] 960 64 (BS2_b3ba934b_RI_Batch_020c9523dfd0.2.2.2.2.2.2.2.2.2.2.2.1)
        (Eq.mpr
          (congrArg (fun n : Nat => ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,7] n = true)
            (show (960 + 64 : Nat) = 1024 from rfl))
          h1024)
    have h896 : ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,7] 896=true :=
      ThreeBoundRecordLookup.checkCasesFrom_step ThreeBoundEndpoint40Records.tree [5,5,5,5,5,7] 896 64 (BS2_b3ba934b_RI_Batch_020c9523dfd0.2.2.2.2.2.2.2.2.2.2.1)
        (Eq.mpr
          (congrArg (fun n : Nat => ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,7] n = true)
            (show (896 + 64 : Nat) = 960 from rfl))
          h960)
    exact h896
  have ri_inline_checked_type6_29_assembly_from640 : ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,7] 640=true := by
    have h832 : ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,7] 832=true :=
      ThreeBoundRecordLookup.checkCasesFrom_step ThreeBoundEndpoint40Records.tree [5,5,5,5,5,7] 832 64 (BS2_b3ba934b_RI_Batch_020c9523dfd0.2.2.2.2.2.2.2.2.2.1)
        (Eq.mpr
          (congrArg (fun n : Nat => ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,7] n = true)
            (show (832 + 64 : Nat) = 896 from rfl))
          ri_inline_checked_type6_29_assembly_from896)
    have h768 : ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,7] 768=true :=
      ThreeBoundRecordLookup.checkCasesFrom_step ThreeBoundEndpoint40Records.tree [5,5,5,5,5,7] 768 64 (BS2_b3ba934b_RI_Batch_020c9523dfd0.2.2.2.2.2.2.2.2.1)
        (Eq.mpr
          (congrArg (fun n : Nat => ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,7] n = true)
            (show (768 + 64 : Nat) = 832 from rfl))
          h832)
    have h704 : ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,7] 704=true :=
      ThreeBoundRecordLookup.checkCasesFrom_step ThreeBoundEndpoint40Records.tree [5,5,5,5,5,7] 704 64 (BS2_b3ba934b_RI_Batch_020c9523dfd0.2.2.2.2.2.2.2.1)
        (Eq.mpr
          (congrArg (fun n : Nat => ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,7] n = true)
            (show (704 + 64 : Nat) = 768 from rfl))
          h768)
    have h640 : ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,7] 640=true :=
      ThreeBoundRecordLookup.checkCasesFrom_step ThreeBoundEndpoint40Records.tree [5,5,5,5,5,7] 640 64 (BS2_b3ba934b_RI_Batch_020c9523dfd0.2.2.2.2.2.2.1)
        (Eq.mpr
          (congrArg (fun n : Nat => ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,7] n = true)
            (show (640 + 64 : Nat) = 704 from rfl))
          h704)
    exact h640
  have ri_inline_checked_type6_29_assembly_from384 : ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,7] 384=true := by
    have h576 : ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,7] 576=true :=
      ThreeBoundRecordLookup.checkCasesFrom_step ThreeBoundEndpoint40Records.tree [5,5,5,5,5,7] 576 64 (BS2_b3ba934b_RI_Batch_020c9523dfd0.2.2.2.2.2.1)
        (Eq.mpr
          (congrArg (fun n : Nat => ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,7] n = true)
            (show (576 + 64 : Nat) = 640 from rfl))
          ri_inline_checked_type6_29_assembly_from640)
    have h512 : ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,7] 512=true :=
      ThreeBoundRecordLookup.checkCasesFrom_step ThreeBoundEndpoint40Records.tree [5,5,5,5,5,7] 512 64 (BS2_b3ba934b_RI_Batch_020c9523dfd0.2.2.2.2.1)
        (Eq.mpr
          (congrArg (fun n : Nat => ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,7] n = true)
            (show (512 + 64 : Nat) = 576 from rfl))
          h576)
    have h448 : ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,7] 448=true :=
      ThreeBoundRecordLookup.checkCasesFrom_step ThreeBoundEndpoint40Records.tree [5,5,5,5,5,7] 448 64 (BS2_b3ba934b_RI_Batch_c0d235b91e7d.2.2.2.2.2.2.2.2.2.2.1)
        (Eq.mpr
          (congrArg (fun n : Nat => ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,7] n = true)
            (show (448 + 64 : Nat) = 512 from rfl))
          h512)
    have h384 : ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,7] 384=true :=
      ThreeBoundRecordLookup.checkCasesFrom_step ThreeBoundEndpoint40Records.tree [5,5,5,5,5,7] 384 64 (BS2_b3ba934b_RI_Batch_c0d235b91e7d.2.2.2.2.2.2.2.2.2.1)
        (Eq.mpr
          (congrArg (fun n : Nat => ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,7] n = true)
            (show (384 + 64 : Nat) = 448 from rfl))
          h448)
    exact h384
  have ri_inline_checked_type6_29_assembly_from128 : ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,7] 128=true := by
    have h320 : ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,7] 320=true :=
      ThreeBoundRecordLookup.checkCasesFrom_step ThreeBoundEndpoint40Records.tree [5,5,5,5,5,7] 320 64 (BS2_b3ba934b_RI_Batch_c0d235b91e7d.2.2.2.2.2.2.2.2.1)
        (Eq.mpr
          (congrArg (fun n : Nat => ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,7] n = true)
            (show (320 + 64 : Nat) = 384 from rfl))
          ri_inline_checked_type6_29_assembly_from384)
    have h256 : ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,7] 256=true :=
      ThreeBoundRecordLookup.checkCasesFrom_step ThreeBoundEndpoint40Records.tree [5,5,5,5,5,7] 256 64 (BS2_b3ba934b_RI_Batch_c0d235b91e7d.2.2.2.2.2.2.2.1)
        (Eq.mpr
          (congrArg (fun n : Nat => ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,7] n = true)
            (show (256 + 64 : Nat) = 320 from rfl))
          h320)
    have h192 : ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,7] 192=true :=
      ThreeBoundRecordLookup.checkCasesFrom_step ThreeBoundEndpoint40Records.tree [5,5,5,5,5,7] 192 64 (BS2_b3ba934b_RI_Batch_c0d235b91e7d.2.2.2.2.2.2.1)
        (Eq.mpr
          (congrArg (fun n : Nat => ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,7] n = true)
            (show (192 + 64 : Nat) = 256 from rfl))
          h256)
    have h128 : ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,7] 128=true :=
      ThreeBoundRecordLookup.checkCasesFrom_step ThreeBoundEndpoint40Records.tree [5,5,5,5,5,7] 128 64 (BS2_b3ba934b_RI_Batch_c0d235b91e7d.2.2.2.2.2.1)
        (Eq.mpr
          (congrArg (fun n : Nat => ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,7] n = true)
            (show (128 + 64 : Nat) = 192 from rfl))
          h192)
    exact h128
  have ri_inline_checked_type6_29_assembly_from0 : ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,7] 0=true := by
    have h64 : ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,7] 64=true :=
      ThreeBoundRecordLookup.checkCasesFrom_step ThreeBoundEndpoint40Records.tree [5,5,5,5,5,7] 64 64 (BS2_b3ba934b_RI_Batch_c0d235b91e7d.2.2.2.2.2.2.2.2.2.2.2.1)
        (Eq.mpr
          (congrArg (fun n : Nat => ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,7] n = true)
            (show (64 + 64 : Nat) = 128 from rfl))
          ri_inline_checked_type6_29_assembly_from128)
    have h0 : ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,7] 0=true :=
      ThreeBoundRecordLookup.checkCasesFrom_step ThreeBoundEndpoint40Records.tree [5,5,5,5,5,7] 0 64 (BS2_b3ba934b_RI_Batch_c0d235b91e7d.2.2.2.2.1)
        (Eq.mpr
          (congrArg (fun n : Nat => ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,7] n = true)
            (show (0 + 64 : Nat) = 64 from rfl))
          h64)
    exact h0
  exact ThreeBoundRecordLookup.checkTypes_of_from ThreeBoundEndpoint40Records.tree [5,5,5,5,5,7] ri_inline_checked_type6_29_assembly_from0
