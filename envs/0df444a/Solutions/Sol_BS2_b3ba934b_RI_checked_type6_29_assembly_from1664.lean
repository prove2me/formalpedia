-- Prove2me | solution 1 for BS2_b3ba934b_RI_checked_type6_29_assembly_from1664
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T19:41:17.563342+00:00
-- url     : https://prove2.me/submissions/894e4de1-01c8-43e4-a9d3-aa787c8cf3e7

import Definitions.Def_BS2_b3ba934b_Endpoint40RecordTreeData
import Definitions.Def_BS2_b3ba934b_RecordChunking
import Theorems.Thm_BS2_b3ba934b_RI_checked_type6_29_assembly_from1920
import Theorems.Thm_BS2_b3ba934b_RI_checked_type6_29_chunk1664
import Theorems.Thm_BS2_b3ba934b_RI_checked_type6_29_chunk1728
import Theorems.Thm_BS2_b3ba934b_RI_checked_type6_29_chunk1792
import Theorems.Thm_BS2_b3ba934b_RI_checked_type6_29_chunk1856
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
open ThreeBoundEndpoint40Records ThreeBoundRecordLookup
attribute [local irreducible] ThreeBoundRecordLookup.checkCasesFrom ThreeBoundRecordLookup.checkCasesChunk ThreeBoundRecordLookup.checkTypes ThreeBoundRecordLookup.checkLength ThreeBoundEndpoint40Records.tree

theorem solution : ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,7] 1664=true := by
  have h1856 : ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,7] 1856=true :=
    ThreeBoundRecordLookup.checkCasesFrom_step ThreeBoundEndpoint40Records.tree [5,5,5,5,5,7] 1856 64 BS2_b3ba934b_RI_checked_type6_29_chunk1856
      (Eq.mpr
        (congrArg (fun n : Nat => ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,7] n = true)
          (show (1856 + 64 : Nat) = 1920 from rfl))
        BS2_b3ba934b_RI_checked_type6_29_assembly_from1920)
  have h1792 : ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,7] 1792=true :=
    ThreeBoundRecordLookup.checkCasesFrom_step ThreeBoundEndpoint40Records.tree [5,5,5,5,5,7] 1792 64 BS2_b3ba934b_RI_checked_type6_29_chunk1792
      (Eq.mpr
        (congrArg (fun n : Nat => ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,7] n = true)
          (show (1792 + 64 : Nat) = 1856 from rfl))
        h1856)
  have h1728 : ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,7] 1728=true :=
    ThreeBoundRecordLookup.checkCasesFrom_step ThreeBoundEndpoint40Records.tree [5,5,5,5,5,7] 1728 64 BS2_b3ba934b_RI_checked_type6_29_chunk1728
      (Eq.mpr
        (congrArg (fun n : Nat => ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,7] n = true)
          (show (1728 + 64 : Nat) = 1792 from rfl))
        h1792)
  have h1664 : ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,7] 1664=true :=
    ThreeBoundRecordLookup.checkCasesFrom_step ThreeBoundEndpoint40Records.tree [5,5,5,5,5,7] 1664 64 BS2_b3ba934b_RI_checked_type6_29_chunk1664
      (Eq.mpr
        (congrArg (fun n : Nat => ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,7] n = true)
          (show (1664 + 64 : Nat) = 1728 from rfl))
        h1728)
  exact h1664
