-- Prove2me | solution 1 for BS2_b3ba934b_RI_checked_type6_29_assembly_from1408
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T19:43:08.043933+00:00
-- url     : https://prove2.me/submissions/7ed845ac-7ebb-4fd9-877e-8b6e6fc33d75

import Definitions.Def_BS2_b3ba934b_Endpoint40RecordTreeData
import Definitions.Def_BS2_b3ba934b_RecordChunking
import Theorems.Thm_BS2_b3ba934b_RI_checked_type6_29_assembly_from1664
import Theorems.Thm_BS2_b3ba934b_RI_checked_type6_29_chunk1408
import Theorems.Thm_BS2_b3ba934b_RI_checked_type6_29_chunk1472
import Theorems.Thm_BS2_b3ba934b_RI_checked_type6_29_chunk1536
import Theorems.Thm_BS2_b3ba934b_RI_checked_type6_29_chunk1600
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
open ThreeBoundEndpoint40Records ThreeBoundRecordLookup
attribute [local irreducible] ThreeBoundRecordLookup.checkCasesFrom ThreeBoundRecordLookup.checkCasesChunk ThreeBoundRecordLookup.checkTypes ThreeBoundRecordLookup.checkLength ThreeBoundEndpoint40Records.tree

theorem solution : ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,7] 1408=true := by
  have h1600 : ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,7] 1600=true :=
    ThreeBoundRecordLookup.checkCasesFrom_step ThreeBoundEndpoint40Records.tree [5,5,5,5,5,7] 1600 64 BS2_b3ba934b_RI_checked_type6_29_chunk1600
      (Eq.mpr
        (congrArg (fun n : Nat => ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,7] n = true)
          (show (1600 + 64 : Nat) = 1664 from rfl))
        BS2_b3ba934b_RI_checked_type6_29_assembly_from1664)
  have h1536 : ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,7] 1536=true :=
    ThreeBoundRecordLookup.checkCasesFrom_step ThreeBoundEndpoint40Records.tree [5,5,5,5,5,7] 1536 64 BS2_b3ba934b_RI_checked_type6_29_chunk1536
      (Eq.mpr
        (congrArg (fun n : Nat => ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,7] n = true)
          (show (1536 + 64 : Nat) = 1600 from rfl))
        h1600)
  have h1472 : ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,7] 1472=true :=
    ThreeBoundRecordLookup.checkCasesFrom_step ThreeBoundEndpoint40Records.tree [5,5,5,5,5,7] 1472 64 BS2_b3ba934b_RI_checked_type6_29_chunk1472
      (Eq.mpr
        (congrArg (fun n : Nat => ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,7] n = true)
          (show (1472 + 64 : Nat) = 1536 from rfl))
        h1536)
  have h1408 : ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,7] 1408=true :=
    ThreeBoundRecordLookup.checkCasesFrom_step ThreeBoundEndpoint40Records.tree [5,5,5,5,5,7] 1408 64 BS2_b3ba934b_RI_checked_type6_29_chunk1408
      (Eq.mpr
        (congrArg (fun n : Nat => ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,7] n = true)
          (show (1408 + 64 : Nat) = 1472 from rfl))
        h1472)
  exact h1408
