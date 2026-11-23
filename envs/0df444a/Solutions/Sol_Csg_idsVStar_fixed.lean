-- Prove2me | solution 1 for Csg.idsVStar_fixed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:57:18.14797+00:00
-- url     : https://prove2.me/submissions/2abb440f-c4c1-4e5b-9fda-78d0fd33b767

import Definitions.Def_Csg_IntrusionDetection
import Definitions.Def_Csg_ReachCertificate
import Definitions.Def_Csg_IntrusionDetectionReach
import Theorems.Thm_Csg_idsGameCSG_stageGame_A
import Theorems.Thm_Csg_CSG_bwInd_zero
import Theorems.Thm_Csg_MatrixGame_le_value_of_forall_le
import Theorems.Thm_Csg_MatrixGame_value_le_of_forall_le
attribute [local simp] Csg.CSG.bwInd_zero



set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution :
    idsGameCSG.reachOp idsGoalHealthy idsGameCSG_r_zero idsVStar = idsVStar := by
  funext s
  apply Subtype.ext
  cases s with
  | healthy => rfl
  | compromised =>
      change (idsGameCSG.stageGame .compromised (fun s' => (idsVStar s' : ℝ))).value =
        (idsVStar .compromised : ℝ)
      have hconst : ∀ a1 a2,
          (idsGameCSG.stageGame .compromised (fun s' => (idsVStar s' : ℝ))).A a1 a2 = 1 := by
        intro a1 a2
        rw [idsGameCSG_stageGame_A]
        simp [idsVStar]
      have hle : (idsGameCSG.stageGame .compromised (fun s' => (idsVStar s' : ℝ))).value ≤ 1 :=
        (idsGameCSG.stageGame .compromised (fun s' => (idsVStar s' : ℝ))).value_le_of_forall_le
          fun a1 a2 => (hconst a1 a2).le
      have hge :
          (1 : ℝ) ≤ (idsGameCSG.stageGame .compromised (fun s' => (idsVStar s' : ℝ))).value :=
        (idsGameCSG.stageGame .compromised (fun s' => (idsVStar s' : ℝ))).le_value_of_forall_le
          fun a1 a2 => (hconst a1 a2).ge
      have hVstar : (idsVStar .compromised : ℝ) = 1 := rfl
      rw [hVstar]
      linarith
end Csg
