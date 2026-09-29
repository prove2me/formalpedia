-- Prove2me | solution 1 for Freiman.lower_physical_cover_distance
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T12:57:52.447887+00:00
-- url     : https://prove2.me/submissions/b85e8957-aadc-45f9-bfbc-e89090c7188a

import Theorems.Thm_Freiman_lower_cover_distance
import Theorems.Thm_Freiman_lower_model_reflection
import Theorems.Thm_Freiman_lower_cylinder_reflection
import Theorems.Thm_Freiman_lower_center_reflection
import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

theorem solution (h : ℕ → LowerPair) (n : ℕ) (hp : lowerAdmissible (h n))
    (a : ℤ → ℕ+) (ha : LowerModel a) (hc : lowerCylinder (lowerPhysicalPath h n) a)
    (t : ℝ) (ht : t ∈ lowerCover (h n)) :
    |localValue a 0-t| ≤ lowerCylinderError (lowerPhysicalPath h n) := by
  by_cases ho : lowerOrientation h n = true
  · have hc' : lowerCylinder (h n).swap a := by simpa [lowerPhysicalPath,ho] using hc
    have hd := lower_cover_distance (h n) hp (fun i : ℤ => a (-i))
      (lower_model_reflection a ha) (lower_cylinder_reflection (h n) a hc') t ht
    rw [lower_center_reflection] at hd
    simpa [lowerPhysicalPath,ho,lowerCylinderError,add_comm] using hd
  · have hf : lowerOrientation h n = false := Bool.eq_false_iff.mpr ho
    have hc' : lowerCylinder (h n) a := by simpa [lowerPhysicalPath,hf] using hc
    simpa [lowerPhysicalPath,hf] using lower_cover_distance (h n) hp a ha hc' t ht
