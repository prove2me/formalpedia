-- Prove2me | solution 2 for Freiman.lower_path_model
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-11T22:05:12.29739+00:00
-- url     : https://prove2.me/submissions/55f47ff0-abb8-4347-ba18-a204e1b9d452

import Definitions.Def_Freiman_lowerCertificates
import Theorems.Thm_Freiman_lower_path_prefixes
import Theorems.Thm_Freiman_lower_nested_cylinders
import Theorems.Thm_Freiman_lower_zero_error_identity
import Theorems.Thm_Freiman_lower_error_tendsto
import Theorems.Thm_Freiman_lower_path_growth
import Theorems.Thm_Freiman_lower_physical_cover_distance

open Freiman

theorem solution (t : ℝ) (h : ℕ → LowerPair) (hh : lowerPath t h) :
    lowerHasValue t := by
  have hprefix := lower_path_prefixes t h hh
  obtain ⟨a, ha, hcyl⟩ := lower_nested_cylinders (lowerPhysicalPath h)
    hprefix.1 hprefix.2.1
  have hgrowth := lower_path_growth t h hh
  have herr := lower_error_tendsto (lowerPhysicalPath h) hgrowth
  have hzero : localValue a 0 = t := by
    apply lower_zero_error_identity (localValue a 0) t
      (fun n => lowerCylinderError (lowerPhysicalPath h n)) herr
    intro n
    have hstate := (hh n).2.1 n (le_refl n)
    exact lower_physical_cover_distance h n hstate.1 a ha (hcyl n) t hstate.2.2.1
  exact ⟨a, ha, hzero⟩
