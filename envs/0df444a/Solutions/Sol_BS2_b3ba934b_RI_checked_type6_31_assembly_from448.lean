-- Prove2me | solution 1 for BS2_b3ba934b_RI_checked_type6_31_assembly_from448
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T19:39:46.022618+00:00
-- url     : https://prove2.me/submissions/65554d86-c420-4087-b5e7-777d9e71b082

import Definitions.Def_BS2_b3ba934b_Endpoint40RecordTreeData
import Definitions.Def_BS2_b3ba934b_RecordChunking
import Theorems.Thm_BS2_b3ba934b_RI_Batch_04e2a8d7543d
import Theorems.Thm_BS2_b3ba934b_RI_checked_type6_31_assembly_end
import Theorems.Thm_BS2_b3ba934b_RI_checked_type6_31_chunk448
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
open ThreeBoundEndpoint40Records ThreeBoundRecordLookup
attribute [local irreducible] ThreeBoundRecordLookup.checkCasesFrom ThreeBoundRecordLookup.checkCasesChunk ThreeBoundRecordLookup.checkTypes ThreeBoundRecordLookup.checkLength ThreeBoundEndpoint40Records.tree

theorem solution : ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,7,7] 448=true := by
  have h640 : ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,7,7] 640=true :=
    ThreeBoundRecordLookup.checkCasesFrom_step ThreeBoundEndpoint40Records.tree [5,5,5,5,7,7] 640 48 (BS2_b3ba934b_RI_Batch_04e2a8d7543d.2.2.1)
      (Eq.mpr
        (congrArg (fun n : Nat => ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,7,7] n = true)
          (show (640 + 48 : Nat) = 688 from rfl))
        BS2_b3ba934b_RI_checked_type6_31_assembly_end)
  have h576 : ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,7,7] 576=true :=
    ThreeBoundRecordLookup.checkCasesFrom_step ThreeBoundEndpoint40Records.tree [5,5,5,5,7,7] 576 64 (BS2_b3ba934b_RI_Batch_04e2a8d7543d.2.1)
      (Eq.mpr
        (congrArg (fun n : Nat => ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,7,7] n = true)
          (show (576 + 64 : Nat) = 640 from rfl))
        h640)
  have h512 : ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,7,7] 512=true :=
    ThreeBoundRecordLookup.checkCasesFrom_step ThreeBoundEndpoint40Records.tree [5,5,5,5,7,7] 512 64 (BS2_b3ba934b_RI_Batch_04e2a8d7543d.1)
      (Eq.mpr
        (congrArg (fun n : Nat => ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,7,7] n = true)
          (show (512 + 64 : Nat) = 576 from rfl))
        h576)
  have h448 : ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,7,7] 448=true :=
    ThreeBoundRecordLookup.checkCasesFrom_step ThreeBoundEndpoint40Records.tree [5,5,5,5,7,7] 448 64 BS2_b3ba934b_RI_checked_type6_31_chunk448
      (Eq.mpr
        (congrArg (fun n : Nat => ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,7,7] n = true)
          (show (448 + 64 : Nat) = 512 from rfl))
        h512)
  exact h448
