-- Prove2me | solution 1 for BS2_b3ba934b_RI_checked_type6_27
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T19:50:08.768548+00:00
-- url     : https://prove2.me/submissions/5d489b03-d48f-4d33-8798-bff32a517d44

import Definitions.Def_BS2_b3ba934b_Endpoint40RecordTreeData
import Definitions.Def_BS2_b3ba934b_RecordChunking
import Theorems.Thm_BS2_b3ba934b_RI_Batch_105f47f95a02
import Theorems.Thm_BS2_b3ba934b_RI_Batch_47945636dd74
import Theorems.Thm_BS2_b3ba934b_RI_Batch_65ca5c1e3af6
import Theorems.Thm_BS2_b3ba934b_RI_Batch_8711957e6e22
import Theorems.Thm_BS2_b3ba934b_RI_Batch_a37056f1e7c5
import Theorems.Thm_BS2_b3ba934b_RI_checked_type6_27_assembly_end
import Theorems.Thm_BS2_b3ba934b_RI_checked_type6_27_chunk3840
import Theorems.Thm_BS2_b3ba934b_RI_checked_type6_27_chunk3904
import Theorems.Thm_BS2_b3ba934b_RI_checked_type6_27_chunk3968
import Theorems.Thm_BS2_b3ba934b_RI_checked_type6_27_chunk4032
import Theorems.Thm_BS2_b3ba934b_RI_checked_type6_27_chunk4096
import Theorems.Thm_BS2_b3ba934b_RI_checked_type6_27_chunk4160
import Theorems.Thm_BS2_b3ba934b_RI_checked_type6_27_chunk4224
import Theorems.Thm_BS2_b3ba934b_RI_checked_type6_27_chunk4288
import Theorems.Thm_BS2_b3ba934b_RI_checked_type6_27_chunk4352
import Theorems.Thm_BS2_b3ba934b_RI_checked_type6_27_chunk4416
import Theorems.Thm_BS2_b3ba934b_RI_checked_type6_27_chunk4480
import Theorems.Thm_BS2_b3ba934b_RI_checked_type6_27_chunk4544
import Theorems.Thm_BS2_b3ba934b_RI_checked_type6_27_chunk4608
import Theorems.Thm_BS2_b3ba934b_RI_checked_type6_27_chunk4672
import Theorems.Thm_BS2_b3ba934b_RI_checked_type6_27_chunk4736
import Theorems.Thm_BS2_b3ba934b_RI_checked_type6_27_chunk4800
import Theorems.Thm_BS2_b3ba934b_RI_checked_type6_27_chunk4864
import Theorems.Thm_BS2_b3ba934b_RI_checked_type6_27_chunk4928
import Theorems.Thm_BS2_b3ba934b_RI_checked_type6_27_chunk4992
import Theorems.Thm_BS2_b3ba934b_RI_checked_type6_27_chunk5056
import Theorems.Thm_BS2_b3ba934b_RI_checked_type6_27_chunk5120
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
open ThreeBoundEndpoint40Records ThreeBoundRecordLookup
attribute [local irreducible] ThreeBoundRecordLookup.checkCasesFrom ThreeBoundRecordLookup.checkCasesChunk ThreeBoundRecordLookup.checkTypes ThreeBoundRecordLookup.checkLength ThreeBoundEndpoint40Records.tree

theorem solution : ThreeBoundRecordLookup.checkTypes ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5]=true := by
  have ri_inline_checked_type6_27_assembly_from4928 : ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 4928=true := by
    have h5120 : ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 5120=true :=
      ThreeBoundRecordLookup.checkCasesFrom_step ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 5120 64 BS2_b3ba934b_RI_checked_type6_27_chunk5120
        (Eq.mpr
          (congrArg (fun n : Nat => ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] n = true)
            (show (5120 + 64 : Nat) = 5184 from rfl))
          BS2_b3ba934b_RI_checked_type6_27_assembly_end)
    have h5056 : ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 5056=true :=
      ThreeBoundRecordLookup.checkCasesFrom_step ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 5056 64 BS2_b3ba934b_RI_checked_type6_27_chunk5056
        (Eq.mpr
          (congrArg (fun n : Nat => ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] n = true)
            (show (5056 + 64 : Nat) = 5120 from rfl))
          h5120)
    have h4992 : ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 4992=true :=
      ThreeBoundRecordLookup.checkCasesFrom_step ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 4992 64 BS2_b3ba934b_RI_checked_type6_27_chunk4992
        (Eq.mpr
          (congrArg (fun n : Nat => ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] n = true)
            (show (4992 + 64 : Nat) = 5056 from rfl))
          h5056)
    have h4928 : ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 4928=true :=
      ThreeBoundRecordLookup.checkCasesFrom_step ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 4928 64 BS2_b3ba934b_RI_checked_type6_27_chunk4928
        (Eq.mpr
          (congrArg (fun n : Nat => ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] n = true)
            (show (4928 + 64 : Nat) = 4992 from rfl))
          h4992)
    exact h4928
  have ri_inline_checked_type6_27_assembly_from4672 : ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 4672=true := by
    have h4864 : ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 4864=true :=
      ThreeBoundRecordLookup.checkCasesFrom_step ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 4864 64 BS2_b3ba934b_RI_checked_type6_27_chunk4864
        (Eq.mpr
          (congrArg (fun n : Nat => ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] n = true)
            (show (4864 + 64 : Nat) = 4928 from rfl))
          ri_inline_checked_type6_27_assembly_from4928)
    have h4800 : ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 4800=true :=
      ThreeBoundRecordLookup.checkCasesFrom_step ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 4800 64 BS2_b3ba934b_RI_checked_type6_27_chunk4800
        (Eq.mpr
          (congrArg (fun n : Nat => ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] n = true)
            (show (4800 + 64 : Nat) = 4864 from rfl))
          h4864)
    have h4736 : ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 4736=true :=
      ThreeBoundRecordLookup.checkCasesFrom_step ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 4736 64 BS2_b3ba934b_RI_checked_type6_27_chunk4736
        (Eq.mpr
          (congrArg (fun n : Nat => ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] n = true)
            (show (4736 + 64 : Nat) = 4800 from rfl))
          h4800)
    have h4672 : ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 4672=true :=
      ThreeBoundRecordLookup.checkCasesFrom_step ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 4672 64 BS2_b3ba934b_RI_checked_type6_27_chunk4672
        (Eq.mpr
          (congrArg (fun n : Nat => ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] n = true)
            (show (4672 + 64 : Nat) = 4736 from rfl))
          h4736)
    exact h4672
  have ri_inline_checked_type6_27_assembly_from4416 : ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 4416=true := by
    have h4608 : ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 4608=true :=
      ThreeBoundRecordLookup.checkCasesFrom_step ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 4608 64 BS2_b3ba934b_RI_checked_type6_27_chunk4608
        (Eq.mpr
          (congrArg (fun n : Nat => ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] n = true)
            (show (4608 + 64 : Nat) = 4672 from rfl))
          ri_inline_checked_type6_27_assembly_from4672)
    have h4544 : ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 4544=true :=
      ThreeBoundRecordLookup.checkCasesFrom_step ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 4544 64 BS2_b3ba934b_RI_checked_type6_27_chunk4544
        (Eq.mpr
          (congrArg (fun n : Nat => ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] n = true)
            (show (4544 + 64 : Nat) = 4608 from rfl))
          h4608)
    have h4480 : ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 4480=true :=
      ThreeBoundRecordLookup.checkCasesFrom_step ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 4480 64 BS2_b3ba934b_RI_checked_type6_27_chunk4480
        (Eq.mpr
          (congrArg (fun n : Nat => ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] n = true)
            (show (4480 + 64 : Nat) = 4544 from rfl))
          h4544)
    have h4416 : ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 4416=true :=
      ThreeBoundRecordLookup.checkCasesFrom_step ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 4416 64 BS2_b3ba934b_RI_checked_type6_27_chunk4416
        (Eq.mpr
          (congrArg (fun n : Nat => ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] n = true)
            (show (4416 + 64 : Nat) = 4480 from rfl))
          h4480)
    exact h4416
  have ri_inline_checked_type6_27_assembly_from4160 : ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 4160=true := by
    have h4352 : ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 4352=true :=
      ThreeBoundRecordLookup.checkCasesFrom_step ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 4352 64 BS2_b3ba934b_RI_checked_type6_27_chunk4352
        (Eq.mpr
          (congrArg (fun n : Nat => ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] n = true)
            (show (4352 + 64 : Nat) = 4416 from rfl))
          ri_inline_checked_type6_27_assembly_from4416)
    have h4288 : ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 4288=true :=
      ThreeBoundRecordLookup.checkCasesFrom_step ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 4288 64 BS2_b3ba934b_RI_checked_type6_27_chunk4288
        (Eq.mpr
          (congrArg (fun n : Nat => ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] n = true)
            (show (4288 + 64 : Nat) = 4352 from rfl))
          h4352)
    have h4224 : ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 4224=true :=
      ThreeBoundRecordLookup.checkCasesFrom_step ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 4224 64 BS2_b3ba934b_RI_checked_type6_27_chunk4224
        (Eq.mpr
          (congrArg (fun n : Nat => ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] n = true)
            (show (4224 + 64 : Nat) = 4288 from rfl))
          h4288)
    have h4160 : ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 4160=true :=
      ThreeBoundRecordLookup.checkCasesFrom_step ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 4160 64 BS2_b3ba934b_RI_checked_type6_27_chunk4160
        (Eq.mpr
          (congrArg (fun n : Nat => ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] n = true)
            (show (4160 + 64 : Nat) = 4224 from rfl))
          h4224)
    exact h4160
  have ri_inline_checked_type6_27_assembly_from3904 : ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 3904=true := by
    have h4096 : ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 4096=true :=
      ThreeBoundRecordLookup.checkCasesFrom_step ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 4096 64 BS2_b3ba934b_RI_checked_type6_27_chunk4096
        (Eq.mpr
          (congrArg (fun n : Nat => ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] n = true)
            (show (4096 + 64 : Nat) = 4160 from rfl))
          ri_inline_checked_type6_27_assembly_from4160)
    have h4032 : ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 4032=true :=
      ThreeBoundRecordLookup.checkCasesFrom_step ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 4032 64 BS2_b3ba934b_RI_checked_type6_27_chunk4032
        (Eq.mpr
          (congrArg (fun n : Nat => ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] n = true)
            (show (4032 + 64 : Nat) = 4096 from rfl))
          h4096)
    have h3968 : ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 3968=true :=
      ThreeBoundRecordLookup.checkCasesFrom_step ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 3968 64 BS2_b3ba934b_RI_checked_type6_27_chunk3968
        (Eq.mpr
          (congrArg (fun n : Nat => ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] n = true)
            (show (3968 + 64 : Nat) = 4032 from rfl))
          h4032)
    have h3904 : ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 3904=true :=
      ThreeBoundRecordLookup.checkCasesFrom_step ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 3904 64 BS2_b3ba934b_RI_checked_type6_27_chunk3904
        (Eq.mpr
          (congrArg (fun n : Nat => ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] n = true)
            (show (3904 + 64 : Nat) = 3968 from rfl))
          h3968)
    exact h3904
  have ri_inline_checked_type6_27_assembly_from3648 : ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 3648=true := by
    have h3840 : ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 3840=true :=
      ThreeBoundRecordLookup.checkCasesFrom_step ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 3840 64 BS2_b3ba934b_RI_checked_type6_27_chunk3840
        (Eq.mpr
          (congrArg (fun n : Nat => ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] n = true)
            (show (3840 + 64 : Nat) = 3904 from rfl))
          ri_inline_checked_type6_27_assembly_from3904)
    have h3776 : ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 3776=true :=
      ThreeBoundRecordLookup.checkCasesFrom_step ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 3776 64 (BS2_b3ba934b_RI_Batch_8711957e6e22.2.2.2.2.2.2.2.2.2.2.2.1)
        (Eq.mpr
          (congrArg (fun n : Nat => ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] n = true)
            (show (3776 + 64 : Nat) = 3840 from rfl))
          h3840)
    have h3712 : ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 3712=true :=
      ThreeBoundRecordLookup.checkCasesFrom_step ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 3712 64 (BS2_b3ba934b_RI_Batch_8711957e6e22.2.2.2.2.2.2.2.2.2.2.1)
        (Eq.mpr
          (congrArg (fun n : Nat => ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] n = true)
            (show (3712 + 64 : Nat) = 3776 from rfl))
          h3776)
    have h3648 : ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 3648=true :=
      ThreeBoundRecordLookup.checkCasesFrom_step ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 3648 64 (BS2_b3ba934b_RI_Batch_8711957e6e22.2.2.2.2.2.2.2.2.2.1)
        (Eq.mpr
          (congrArg (fun n : Nat => ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] n = true)
            (show (3648 + 64 : Nat) = 3712 from rfl))
          h3712)
    exact h3648
  have ri_inline_checked_type6_27_assembly_from3392 : ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 3392=true := by
    have h3584 : ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 3584=true :=
      ThreeBoundRecordLookup.checkCasesFrom_step ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 3584 64 (BS2_b3ba934b_RI_Batch_8711957e6e22.2.2.2.2.2.2.2.2.1)
        (Eq.mpr
          (congrArg (fun n : Nat => ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] n = true)
            (show (3584 + 64 : Nat) = 3648 from rfl))
          ri_inline_checked_type6_27_assembly_from3648)
    have h3520 : ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 3520=true :=
      ThreeBoundRecordLookup.checkCasesFrom_step ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 3520 64 (BS2_b3ba934b_RI_Batch_8711957e6e22.2.2.2.2.2.2.2.1)
        (Eq.mpr
          (congrArg (fun n : Nat => ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] n = true)
            (show (3520 + 64 : Nat) = 3584 from rfl))
          h3584)
    have h3456 : ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 3456=true :=
      ThreeBoundRecordLookup.checkCasesFrom_step ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 3456 64 (BS2_b3ba934b_RI_Batch_8711957e6e22.2.2.2.2.2.2.1)
        (Eq.mpr
          (congrArg (fun n : Nat => ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] n = true)
            (show (3456 + 64 : Nat) = 3520 from rfl))
          h3520)
    have h3392 : ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 3392=true :=
      ThreeBoundRecordLookup.checkCasesFrom_step ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 3392 64 (BS2_b3ba934b_RI_Batch_8711957e6e22.2.2.2.2.2.1)
        (Eq.mpr
          (congrArg (fun n : Nat => ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] n = true)
            (show (3392 + 64 : Nat) = 3456 from rfl))
          h3456)
    exact h3392
  have ri_inline_checked_type6_27_assembly_from3136 : ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 3136=true := by
    have h3328 : ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 3328=true :=
      ThreeBoundRecordLookup.checkCasesFrom_step ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 3328 64 (BS2_b3ba934b_RI_Batch_8711957e6e22.2.2.2.2.1)
        (Eq.mpr
          (congrArg (fun n : Nat => ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] n = true)
            (show (3328 + 64 : Nat) = 3392 from rfl))
          ri_inline_checked_type6_27_assembly_from3392)
    have h3264 : ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 3264=true :=
      ThreeBoundRecordLookup.checkCasesFrom_step ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 3264 64 (BS2_b3ba934b_RI_Batch_8711957e6e22.2.2.2.1)
        (Eq.mpr
          (congrArg (fun n : Nat => ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] n = true)
            (show (3264 + 64 : Nat) = 3328 from rfl))
          h3328)
    have h3200 : ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 3200=true :=
      ThreeBoundRecordLookup.checkCasesFrom_step ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 3200 64 (BS2_b3ba934b_RI_Batch_8711957e6e22.2.2.1)
        (Eq.mpr
          (congrArg (fun n : Nat => ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] n = true)
            (show (3200 + 64 : Nat) = 3264 from rfl))
          h3264)
    have h3136 : ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 3136=true :=
      ThreeBoundRecordLookup.checkCasesFrom_step ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 3136 64 (BS2_b3ba934b_RI_Batch_8711957e6e22.2.1)
        (Eq.mpr
          (congrArg (fun n : Nat => ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] n = true)
            (show (3136 + 64 : Nat) = 3200 from rfl))
          h3200)
    exact h3136
  have ri_inline_checked_type6_27_assembly_from2880 : ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 2880=true := by
    have h3072 : ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 3072=true :=
      ThreeBoundRecordLookup.checkCasesFrom_step ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 3072 64 (BS2_b3ba934b_RI_Batch_8711957e6e22.1)
        (Eq.mpr
          (congrArg (fun n : Nat => ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] n = true)
            (show (3072 + 64 : Nat) = 3136 from rfl))
          ri_inline_checked_type6_27_assembly_from3136)
    have h3008 : ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 3008=true :=
      ThreeBoundRecordLookup.checkCasesFrom_step ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 3008 64 (BS2_b3ba934b_RI_Batch_65ca5c1e3af6.2.2.2.2.2.2.2.2.2.2.2.1)
        (Eq.mpr
          (congrArg (fun n : Nat => ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] n = true)
            (show (3008 + 64 : Nat) = 3072 from rfl))
          h3072)
    have h2944 : ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 2944=true :=
      ThreeBoundRecordLookup.checkCasesFrom_step ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 2944 64 (BS2_b3ba934b_RI_Batch_65ca5c1e3af6.2.2.2.2.2.2.2.2.2.2.1)
        (Eq.mpr
          (congrArg (fun n : Nat => ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] n = true)
            (show (2944 + 64 : Nat) = 3008 from rfl))
          h3008)
    have h2880 : ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 2880=true :=
      ThreeBoundRecordLookup.checkCasesFrom_step ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 2880 64 (BS2_b3ba934b_RI_Batch_65ca5c1e3af6.2.2.2.2.2.2.2.2.2.1)
        (Eq.mpr
          (congrArg (fun n : Nat => ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] n = true)
            (show (2880 + 64 : Nat) = 2944 from rfl))
          h2944)
    exact h2880
  have ri_inline_checked_type6_27_assembly_from2624 : ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 2624=true := by
    have h2816 : ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 2816=true :=
      ThreeBoundRecordLookup.checkCasesFrom_step ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 2816 64 (BS2_b3ba934b_RI_Batch_65ca5c1e3af6.2.2.2.2.2.2.2.2.1)
        (Eq.mpr
          (congrArg (fun n : Nat => ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] n = true)
            (show (2816 + 64 : Nat) = 2880 from rfl))
          ri_inline_checked_type6_27_assembly_from2880)
    have h2752 : ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 2752=true :=
      ThreeBoundRecordLookup.checkCasesFrom_step ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 2752 64 (BS2_b3ba934b_RI_Batch_65ca5c1e3af6.2.2.2.2.2.2.2.1)
        (Eq.mpr
          (congrArg (fun n : Nat => ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] n = true)
            (show (2752 + 64 : Nat) = 2816 from rfl))
          h2816)
    have h2688 : ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 2688=true :=
      ThreeBoundRecordLookup.checkCasesFrom_step ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 2688 64 (BS2_b3ba934b_RI_Batch_65ca5c1e3af6.2.2.2.2.2.2.1)
        (Eq.mpr
          (congrArg (fun n : Nat => ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] n = true)
            (show (2688 + 64 : Nat) = 2752 from rfl))
          h2752)
    have h2624 : ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 2624=true :=
      ThreeBoundRecordLookup.checkCasesFrom_step ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 2624 64 (BS2_b3ba934b_RI_Batch_65ca5c1e3af6.2.2.2.2.2.1)
        (Eq.mpr
          (congrArg (fun n : Nat => ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] n = true)
            (show (2624 + 64 : Nat) = 2688 from rfl))
          h2688)
    exact h2624
  have ri_inline_checked_type6_27_assembly_from2368 : ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 2368=true := by
    have h2560 : ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 2560=true :=
      ThreeBoundRecordLookup.checkCasesFrom_step ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 2560 64 (BS2_b3ba934b_RI_Batch_65ca5c1e3af6.2.2.2.2.1)
        (Eq.mpr
          (congrArg (fun n : Nat => ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] n = true)
            (show (2560 + 64 : Nat) = 2624 from rfl))
          ri_inline_checked_type6_27_assembly_from2624)
    have h2496 : ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 2496=true :=
      ThreeBoundRecordLookup.checkCasesFrom_step ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 2496 64 (BS2_b3ba934b_RI_Batch_65ca5c1e3af6.2.2.2.1)
        (Eq.mpr
          (congrArg (fun n : Nat => ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] n = true)
            (show (2496 + 64 : Nat) = 2560 from rfl))
          h2560)
    have h2432 : ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 2432=true :=
      ThreeBoundRecordLookup.checkCasesFrom_step ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 2432 64 (BS2_b3ba934b_RI_Batch_65ca5c1e3af6.2.2.1)
        (Eq.mpr
          (congrArg (fun n : Nat => ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] n = true)
            (show (2432 + 64 : Nat) = 2496 from rfl))
          h2496)
    have h2368 : ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 2368=true :=
      ThreeBoundRecordLookup.checkCasesFrom_step ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 2368 64 (BS2_b3ba934b_RI_Batch_65ca5c1e3af6.2.1)
        (Eq.mpr
          (congrArg (fun n : Nat => ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] n = true)
            (show (2368 + 64 : Nat) = 2432 from rfl))
          h2432)
    exact h2368
  have ri_inline_checked_type6_27_assembly_from2112 : ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 2112=true := by
    have h2304 : ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 2304=true :=
      ThreeBoundRecordLookup.checkCasesFrom_step ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 2304 64 (BS2_b3ba934b_RI_Batch_65ca5c1e3af6.1)
        (Eq.mpr
          (congrArg (fun n : Nat => ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] n = true)
            (show (2304 + 64 : Nat) = 2368 from rfl))
          ri_inline_checked_type6_27_assembly_from2368)
    have h2240 : ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 2240=true :=
      ThreeBoundRecordLookup.checkCasesFrom_step ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 2240 64 (BS2_b3ba934b_RI_Batch_a37056f1e7c5.2.2.2.2.2.2.2.2.2.2.2.1)
        (Eq.mpr
          (congrArg (fun n : Nat => ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] n = true)
            (show (2240 + 64 : Nat) = 2304 from rfl))
          h2304)
    have h2176 : ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 2176=true :=
      ThreeBoundRecordLookup.checkCasesFrom_step ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 2176 64 (BS2_b3ba934b_RI_Batch_a37056f1e7c5.2.2.2.2.2.2.2.2.2.2.1)
        (Eq.mpr
          (congrArg (fun n : Nat => ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] n = true)
            (show (2176 + 64 : Nat) = 2240 from rfl))
          h2240)
    have h2112 : ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 2112=true :=
      ThreeBoundRecordLookup.checkCasesFrom_step ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 2112 64 (BS2_b3ba934b_RI_Batch_a37056f1e7c5.2.2.2.2.2.2.2.2.2.1)
        (Eq.mpr
          (congrArg (fun n : Nat => ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] n = true)
            (show (2112 + 64 : Nat) = 2176 from rfl))
          h2176)
    exact h2112
  have ri_inline_checked_type6_27_assembly_from1856 : ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 1856=true := by
    have h2048 : ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 2048=true :=
      ThreeBoundRecordLookup.checkCasesFrom_step ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 2048 64 (BS2_b3ba934b_RI_Batch_a37056f1e7c5.2.2.2.2.2.2.2.2.1)
        (Eq.mpr
          (congrArg (fun n : Nat => ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] n = true)
            (show (2048 + 64 : Nat) = 2112 from rfl))
          ri_inline_checked_type6_27_assembly_from2112)
    have h1984 : ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 1984=true :=
      ThreeBoundRecordLookup.checkCasesFrom_step ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 1984 64 (BS2_b3ba934b_RI_Batch_a37056f1e7c5.2.2.2.2.2.2.2.1)
        (Eq.mpr
          (congrArg (fun n : Nat => ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] n = true)
            (show (1984 + 64 : Nat) = 2048 from rfl))
          h2048)
    have h1920 : ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 1920=true :=
      ThreeBoundRecordLookup.checkCasesFrom_step ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 1920 64 (BS2_b3ba934b_RI_Batch_a37056f1e7c5.2.2.2.2.2.2.1)
        (Eq.mpr
          (congrArg (fun n : Nat => ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] n = true)
            (show (1920 + 64 : Nat) = 1984 from rfl))
          h1984)
    have h1856 : ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 1856=true :=
      ThreeBoundRecordLookup.checkCasesFrom_step ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 1856 64 (BS2_b3ba934b_RI_Batch_a37056f1e7c5.2.2.2.2.2.1)
        (Eq.mpr
          (congrArg (fun n : Nat => ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] n = true)
            (show (1856 + 64 : Nat) = 1920 from rfl))
          h1920)
    exact h1856
  have ri_inline_checked_type6_27_assembly_from1600 : ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 1600=true := by
    have h1792 : ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 1792=true :=
      ThreeBoundRecordLookup.checkCasesFrom_step ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 1792 64 (BS2_b3ba934b_RI_Batch_a37056f1e7c5.2.2.2.2.1)
        (Eq.mpr
          (congrArg (fun n : Nat => ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] n = true)
            (show (1792 + 64 : Nat) = 1856 from rfl))
          ri_inline_checked_type6_27_assembly_from1856)
    have h1728 : ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 1728=true :=
      ThreeBoundRecordLookup.checkCasesFrom_step ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 1728 64 (BS2_b3ba934b_RI_Batch_a37056f1e7c5.2.2.2.1)
        (Eq.mpr
          (congrArg (fun n : Nat => ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] n = true)
            (show (1728 + 64 : Nat) = 1792 from rfl))
          h1792)
    have h1664 : ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 1664=true :=
      ThreeBoundRecordLookup.checkCasesFrom_step ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 1664 64 (BS2_b3ba934b_RI_Batch_a37056f1e7c5.2.2.1)
        (Eq.mpr
          (congrArg (fun n : Nat => ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] n = true)
            (show (1664 + 64 : Nat) = 1728 from rfl))
          h1728)
    have h1600 : ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 1600=true :=
      ThreeBoundRecordLookup.checkCasesFrom_step ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 1600 64 (BS2_b3ba934b_RI_Batch_a37056f1e7c5.2.1)
        (Eq.mpr
          (congrArg (fun n : Nat => ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] n = true)
            (show (1600 + 64 : Nat) = 1664 from rfl))
          h1664)
    exact h1600
  have ri_inline_checked_type6_27_assembly_from1344 : ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 1344=true := by
    have h1536 : ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 1536=true :=
      ThreeBoundRecordLookup.checkCasesFrom_step ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 1536 64 (BS2_b3ba934b_RI_Batch_a37056f1e7c5.1)
        (Eq.mpr
          (congrArg (fun n : Nat => ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] n = true)
            (show (1536 + 64 : Nat) = 1600 from rfl))
          ri_inline_checked_type6_27_assembly_from1600)
    have h1472 : ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 1472=true :=
      ThreeBoundRecordLookup.checkCasesFrom_step ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 1472 64 (BS2_b3ba934b_RI_Batch_47945636dd74.2.2.2.2.2.2.2.1)
        (Eq.mpr
          (congrArg (fun n : Nat => ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] n = true)
            (show (1472 + 64 : Nat) = 1536 from rfl))
          h1536)
    have h1408 : ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 1408=true :=
      ThreeBoundRecordLookup.checkCasesFrom_step ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 1408 64 (BS2_b3ba934b_RI_Batch_47945636dd74.2.2.2.2.2.2.1)
        (Eq.mpr
          (congrArg (fun n : Nat => ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] n = true)
            (show (1408 + 64 : Nat) = 1472 from rfl))
          h1472)
    have h1344 : ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 1344=true :=
      ThreeBoundRecordLookup.checkCasesFrom_step ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 1344 64 (BS2_b3ba934b_RI_Batch_47945636dd74.2.2.2.2.2.1)
        (Eq.mpr
          (congrArg (fun n : Nat => ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] n = true)
            (show (1344 + 64 : Nat) = 1408 from rfl))
          h1408)
    exact h1344
  have ri_inline_checked_type6_27_assembly_from1088 : ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 1088=true := by
    have h1280 : ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 1280=true :=
      ThreeBoundRecordLookup.checkCasesFrom_step ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 1280 64 (BS2_b3ba934b_RI_Batch_47945636dd74.2.2.2.2.1)
        (Eq.mpr
          (congrArg (fun n : Nat => ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] n = true)
            (show (1280 + 64 : Nat) = 1344 from rfl))
          ri_inline_checked_type6_27_assembly_from1344)
    have h1216 : ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 1216=true :=
      ThreeBoundRecordLookup.checkCasesFrom_step ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 1216 64 (BS2_b3ba934b_RI_Batch_47945636dd74.2.2.2.1)
        (Eq.mpr
          (congrArg (fun n : Nat => ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] n = true)
            (show (1216 + 64 : Nat) = 1280 from rfl))
          h1280)
    have h1152 : ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 1152=true :=
      ThreeBoundRecordLookup.checkCasesFrom_step ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 1152 64 (BS2_b3ba934b_RI_Batch_47945636dd74.2.2.1)
        (Eq.mpr
          (congrArg (fun n : Nat => ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] n = true)
            (show (1152 + 64 : Nat) = 1216 from rfl))
          h1216)
    have h1088 : ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 1088=true :=
      ThreeBoundRecordLookup.checkCasesFrom_step ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 1088 64 (BS2_b3ba934b_RI_Batch_47945636dd74.2.1)
        (Eq.mpr
          (congrArg (fun n : Nat => ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] n = true)
            (show (1088 + 64 : Nat) = 1152 from rfl))
          h1152)
    exact h1088
  have ri_inline_checked_type6_27_assembly_from832 : ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 832=true := by
    have h1024 : ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 1024=true :=
      ThreeBoundRecordLookup.checkCasesFrom_step ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 1024 64 (BS2_b3ba934b_RI_Batch_47945636dd74.1)
        (Eq.mpr
          (congrArg (fun n : Nat => ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] n = true)
            (show (1024 + 64 : Nat) = 1088 from rfl))
          ri_inline_checked_type6_27_assembly_from1088)
    have h960 : ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 960=true :=
      ThreeBoundRecordLookup.checkCasesFrom_step ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 960 64 (BS2_b3ba934b_RI_Batch_47945636dd74.2.2.2.2.2.2.2.2.2.2.2.1)
        (Eq.mpr
          (congrArg (fun n : Nat => ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] n = true)
            (show (960 + 64 : Nat) = 1024 from rfl))
          h1024)
    have h896 : ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 896=true :=
      ThreeBoundRecordLookup.checkCasesFrom_step ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 896 64 (BS2_b3ba934b_RI_Batch_47945636dd74.2.2.2.2.2.2.2.2.2.2.1)
        (Eq.mpr
          (congrArg (fun n : Nat => ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] n = true)
            (show (896 + 64 : Nat) = 960 from rfl))
          h960)
    have h832 : ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 832=true :=
      ThreeBoundRecordLookup.checkCasesFrom_step ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 832 64 (BS2_b3ba934b_RI_Batch_47945636dd74.2.2.2.2.2.2.2.2.2.1)
        (Eq.mpr
          (congrArg (fun n : Nat => ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] n = true)
            (show (832 + 64 : Nat) = 896 from rfl))
          h896)
    exact h832
  have ri_inline_checked_type6_27_assembly_from576 : ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 576=true := by
    have h768 : ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 768=true :=
      ThreeBoundRecordLookup.checkCasesFrom_step ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 768 64 (BS2_b3ba934b_RI_Batch_47945636dd74.2.2.2.2.2.2.2.2.1)
        (Eq.mpr
          (congrArg (fun n : Nat => ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] n = true)
            (show (768 + 64 : Nat) = 832 from rfl))
          ri_inline_checked_type6_27_assembly_from832)
    have h704 : ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 704=true :=
      ThreeBoundRecordLookup.checkCasesFrom_step ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 704 64 (BS2_b3ba934b_RI_Batch_105f47f95a02.2.2.2.2.2.2.2.2.2.2.2.1)
        (Eq.mpr
          (congrArg (fun n : Nat => ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] n = true)
            (show (704 + 64 : Nat) = 768 from rfl))
          h768)
    have h640 : ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 640=true :=
      ThreeBoundRecordLookup.checkCasesFrom_step ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 640 64 (BS2_b3ba934b_RI_Batch_105f47f95a02.2.2.2.2.2.2.2.2.2.2.1)
        (Eq.mpr
          (congrArg (fun n : Nat => ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] n = true)
            (show (640 + 64 : Nat) = 704 from rfl))
          h704)
    have h576 : ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 576=true :=
      ThreeBoundRecordLookup.checkCasesFrom_step ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 576 64 (BS2_b3ba934b_RI_Batch_105f47f95a02.2.2.2.2.2.2.2.2.1)
        (Eq.mpr
          (congrArg (fun n : Nat => ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] n = true)
            (show (576 + 64 : Nat) = 640 from rfl))
          h640)
    exact h576
  have ri_inline_checked_type6_27_assembly_from320 : ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 320=true := by
    have h512 : ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 512=true :=
      ThreeBoundRecordLookup.checkCasesFrom_step ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 512 64 (BS2_b3ba934b_RI_Batch_105f47f95a02.2.2.2.2.2.2.2.1)
        (Eq.mpr
          (congrArg (fun n : Nat => ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] n = true)
            (show (512 + 64 : Nat) = 576 from rfl))
          ri_inline_checked_type6_27_assembly_from576)
    have h448 : ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 448=true :=
      ThreeBoundRecordLookup.checkCasesFrom_step ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 448 64 (BS2_b3ba934b_RI_Batch_105f47f95a02.2.2.2.2.2.2.1)
        (Eq.mpr
          (congrArg (fun n : Nat => ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] n = true)
            (show (448 + 64 : Nat) = 512 from rfl))
          h512)
    have h384 : ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 384=true :=
      ThreeBoundRecordLookup.checkCasesFrom_step ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 384 64 (BS2_b3ba934b_RI_Batch_105f47f95a02.2.2.2.2.2.1)
        (Eq.mpr
          (congrArg (fun n : Nat => ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] n = true)
            (show (384 + 64 : Nat) = 448 from rfl))
          h448)
    have h320 : ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 320=true :=
      ThreeBoundRecordLookup.checkCasesFrom_step ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 320 64 (BS2_b3ba934b_RI_Batch_105f47f95a02.2.2.2.2.1)
        (Eq.mpr
          (congrArg (fun n : Nat => ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] n = true)
            (show (320 + 64 : Nat) = 384 from rfl))
          h384)
    exact h320
  have ri_inline_checked_type6_27_assembly_from64 : ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 64=true := by
    have h256 : ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 256=true :=
      ThreeBoundRecordLookup.checkCasesFrom_step ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 256 64 (BS2_b3ba934b_RI_Batch_105f47f95a02.2.2.2.1)
        (Eq.mpr
          (congrArg (fun n : Nat => ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] n = true)
            (show (256 + 64 : Nat) = 320 from rfl))
          ri_inline_checked_type6_27_assembly_from320)
    have h192 : ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 192=true :=
      ThreeBoundRecordLookup.checkCasesFrom_step ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 192 64 (BS2_b3ba934b_RI_Batch_105f47f95a02.2.2.1)
        (Eq.mpr
          (congrArg (fun n : Nat => ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] n = true)
            (show (192 + 64 : Nat) = 256 from rfl))
          h256)
    have h128 : ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 128=true :=
      ThreeBoundRecordLookup.checkCasesFrom_step ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 128 64 (BS2_b3ba934b_RI_Batch_105f47f95a02.2.1)
        (Eq.mpr
          (congrArg (fun n : Nat => ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] n = true)
            (show (128 + 64 : Nat) = 192 from rfl))
          h192)
    have h64 : ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 64=true :=
      ThreeBoundRecordLookup.checkCasesFrom_step ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 64 64 (BS2_b3ba934b_RI_Batch_105f47f95a02.2.2.2.2.2.2.2.2.2.1)
        (Eq.mpr
          (congrArg (fun n : Nat => ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] n = true)
            (show (64 + 64 : Nat) = 128 from rfl))
          h128)
    exact h64
  have ri_inline_checked_type6_27_assembly_from0 : ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 0=true := by
    have h0 : ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 0=true :=
      ThreeBoundRecordLookup.checkCasesFrom_step ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] 0 64 (BS2_b3ba934b_RI_Batch_105f47f95a02.1)
        (Eq.mpr
          (congrArg (fun n : Nat => ThreeBoundRecordLookup.checkCasesFrom ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] n = true)
            (show (0 + 64 : Nat) = 64 from rfl))
          ri_inline_checked_type6_27_assembly_from64)
    exact h0
  exact ThreeBoundRecordLookup.checkTypes_of_from ThreeBoundEndpoint40Records.tree [5,5,5,5,5,5] ri_inline_checked_type6_27_assembly_from0
