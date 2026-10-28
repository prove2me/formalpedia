-- Prove2me | solution 1 for BS2_b3ba934b_RI_checked_type6_30_assembly_from0
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T19:39:46.114748+00:00
-- url     : https://prove2.me/submissions/92ed67cc-1eb4-4793-82eb-f350b242e1ea

import Definitions.Def_BS2_b3ba934b_Endpoint40RecordTreeData
import Definitions.Def_BS2_b3ba934b_RecordChunking
import Theorems.Thm_BS2_b3ba934b_RI_checked_type6_30_assembly_end
import Theorems.Thm_BS2_b3ba934b_RI_checked_type6_30_chunk0
import Theorems.Thm_BS2_b3ba934b_RI_checked_type6_30_chunk64
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
open ThreeBoundEndpoint40Records ThreeBoundRecordLookup
attribute [local irreducible] ThreeBoundRecordLookup.checkCasesFrom ThreeBoundRecordLookup.checkCasesChunk ThreeBoundRecordLookup.checkTypes ThreeBoundRecordLookup.checkLength ThreeBoundEndpoint40Records.tree

theorem solution : ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,6,7] 0=true := by
  have h64 : ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,6,7] 64=true :=
    ThreeBoundRecordLookup.checkCasesFrom_step ThreeBoundEndpoint40Records.tree [5,5,5,5,6,7] 64 16 BS2_b3ba934b_RI_checked_type6_30_chunk64
      (Eq.mpr
        (congrArg (fun n : Nat => ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,6,7] n = true)
          (show (64 + 16 : Nat) = 80 from rfl))
        BS2_b3ba934b_RI_checked_type6_30_assembly_end)
  have h0 : ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,6,7] 0=true :=
    ThreeBoundRecordLookup.checkCasesFrom_step ThreeBoundEndpoint40Records.tree [5,5,5,5,6,7] 0 64 BS2_b3ba934b_RI_checked_type6_30_chunk0
      (Eq.mpr
        (congrArg (fun n : Nat => ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,6,7] n = true)
          (show (0 + 64 : Nat) = 64 from rfl))
        h64)
  exact h0
