-- Prove2me | solution 2 for Freiman.lower_models
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-11T21:50:44.605645+00:00
-- url     : https://prove2.me/submissions/a3b26e04-7bb6-40b8-af10-f652ed568371

import Definitions.Def_Freiman_lowerCertificates
import Theorems.Thm_Freiman_lower_initial_entry
import Theorems.Thm_Freiman_lower_refinement_alternative
import Theorems.Thm_Freiman_lower_path_model

open Freiman

theorem solution (t : ℝ) (ht : t ∈ Set.Icc cF (Real.sqrt 21)) : lowerHasValue t := by
  rcases lower_initial_entry t ht with hvalue | ⟨p, hroot, hstate⟩
  · exact hvalue
  rcases lower_refinement_alternative t p hroot hstate with hvalue | ⟨h, hpath⟩
  · exact hvalue
  exact lower_path_model t h hpath
