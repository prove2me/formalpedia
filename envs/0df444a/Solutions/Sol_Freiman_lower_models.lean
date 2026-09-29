-- Prove2me | solution 1 for Freiman.lower_models
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T12:56:34.537249+00:00
-- url     : https://prove2.me/submissions/1a605d3c-8c7c-433e-b7ca-cddb08998284

import Theorems.Thm_Freiman_lower_initial_entry
import Theorems.Thm_Freiman_lower_refinement_alternative
import Theorems.Thm_Freiman_lower_path_model
import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

theorem solution (t : ℝ) (ht : t ∈ Set.Icc cF (Real.sqrt 21)) : lowerHasValue t := by
  rcases lower_initial_entry t ht with he | ⟨p,hr,hs⟩
  · exact he
  · rcases lower_refinement_alternative t p hr hs with he | ⟨h,hh⟩
    · exact he
    · exact lower_path_model t h hh
