-- Prove2me | solution 1 for Csg.idsVStar_le_of_prefixed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:00:48.755358+00:00
-- url     : https://prove2.me/submissions/c431de56-f316-4de8-ac51-68cf3f3f0454

import Definitions.Def_Csg_IntrusionDetection
import Definitions.Def_Csg_ReachCertificate
import Definitions.Def_Csg_IntrusionDetectionReach
import Theorems.Thm_Csg_idsGameCSG_compromised_stageValue
import Theorems.Thm_Csg_CSG_bwInd_zero
attribute [local simp] Csg.CSG.bwInd_zero



set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution {b : IDSState → Set.Icc (0 : ℝ) 1}
    (hb : idsGameCSG.reachOp idsGoalHealthy idsGameCSG_r_zero b ≤ b) : idsVStar ≤ b := by
  have hhealthy : (b .healthy : ℝ) = 1 := by
    have hle : (1 : ℝ) ≤ (b .healthy : ℝ) := hb .healthy
    exact le_antisymm (b .healthy).2.2 hle
  have hcomp_le :
      idsGameCSG.stageValue .compromised (fun s' => (b s' : ℝ)) ≤ (b .compromised : ℝ) :=
    hb .compromised
  rw [idsGameCSG_compromised_stageValue, hhealthy] at hcomp_le
  have hcomp_ge : (1 : ℝ) ≤ (b .compromised : ℝ) := by linarith
  intro s
  cases s with
  | healthy =>
      change (idsVStar .healthy : ℝ) ≤ (b .healthy : ℝ)
      simp only [idsVStar]
      linarith
  | compromised =>
      change (idsVStar .compromised : ℝ) ≤ (b .compromised : ℝ)
      simp only [idsVStar]
      linarith
end Csg
