-- Prove2me | solution 1 for Freiman.lower_initial_seams
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T12:55:37.952422+00:00
-- url     : https://prove2.me/submissions/74fa951f-1a15-491c-bce9-28adb08ba4e5

import Theorems.Thm_Freiman_lower_initial_seam_A
import Theorems.Thm_Freiman_lower_initial_seam_C
import Theorems.Thm_Freiman_lower_initial_seam_B18
import Theorems.Thm_Freiman_lower_initial_seam_B19
import Theorems.Thm_Freiman_lower_initial_seam_n13
import Theorems.Thm_Freiman_lower_initial_seam_n14
import Theorems.Thm_Freiman_lower_initial_seam_aux
import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

theorem solution : lowerInitialSeams := by
  exact ⟨lower_initial_seam_A, lower_initial_seam_C, lower_initial_seam_B18, lower_initial_seam_B19, lower_initial_seam_n13, lower_initial_seam_n14, lower_initial_seam_aux⟩
