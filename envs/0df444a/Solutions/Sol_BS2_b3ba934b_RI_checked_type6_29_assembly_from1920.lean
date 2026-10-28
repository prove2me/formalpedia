-- Prove2me | solution 1 for BS2_b3ba934b_RI_checked_type6_29_assembly_from1920
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T19:39:50.52345+00:00
-- url     : https://prove2.me/submissions/67ccdb2d-8d85-4578-a2a6-c5d3e1ec8cc6

import Definitions.Def_BS2_b3ba934b_Endpoint40RecordTreeData
import Definitions.Def_BS2_b3ba934b_RecordChunking
import Theorems.Thm_BS2_b3ba934b_RI_checked_type6_29_assembly_end
import Theorems.Thm_BS2_b3ba934b_RI_checked_type6_29_chunk1920
import Theorems.Thm_BS2_b3ba934b_RI_checked_type6_29_chunk1984
import Theorems.Thm_BS2_b3ba934b_RI_checked_type6_29_chunk2048
import Theorems.Thm_BS2_b3ba934b_RI_checked_type6_29_chunk2112
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
open ThreeBoundEndpoint40Records ThreeBoundRecordLookup
attribute [local irreducible] ThreeBoundRecordLookup.checkCasesFrom ThreeBoundRecordLookup.checkCasesChunk ThreeBoundRecordLookup.checkTypes ThreeBoundRecordLookup.checkLength ThreeBoundEndpoint40Records.tree

theorem solution : ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,7] 1920=true := by
  have h2112 : ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,7] 2112=true :=
    ThreeBoundRecordLookup.checkCasesFrom_step ThreeBoundEndpoint40Records.tree [5,5,5,5,5,7] 2112 32 BS2_b3ba934b_RI_checked_type6_29_chunk2112
      (Eq.mpr
        (congrArg (fun n : Nat => ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,7] n = true)
          (show (2112 + 32 : Nat) = 2144 from rfl))
        BS2_b3ba934b_RI_checked_type6_29_assembly_end)
  have h2048 : ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,7] 2048=true :=
    ThreeBoundRecordLookup.checkCasesFrom_step ThreeBoundEndpoint40Records.tree [5,5,5,5,5,7] 2048 64 BS2_b3ba934b_RI_checked_type6_29_chunk2048
      (Eq.mpr
        (congrArg (fun n : Nat => ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,7] n = true)
          (show (2048 + 64 : Nat) = 2112 from rfl))
        h2112)
  have h1984 : ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,7] 1984=true :=
    ThreeBoundRecordLookup.checkCasesFrom_step ThreeBoundEndpoint40Records.tree [5,5,5,5,5,7] 1984 64 BS2_b3ba934b_RI_checked_type6_29_chunk1984
      (Eq.mpr
        (congrArg (fun n : Nat => ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,7] n = true)
          (show (1984 + 64 : Nat) = 2048 from rfl))
        h2048)
  have h1920 : ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,7] 1920=true :=
    ThreeBoundRecordLookup.checkCasesFrom_step ThreeBoundEndpoint40Records.tree [5,5,5,5,5,7] 1920 64 BS2_b3ba934b_RI_checked_type6_29_chunk1920
      (Eq.mpr
        (congrArg (fun n : Nat => ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,7] n = true)
          (show (1920 + 64 : Nat) = 1984 from rfl))
        h1984)
  exact h1920
