-- Prove2me | solution 1 for Freiman.section14_state_sound
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T13:13:23.762998+00:00
-- url     : https://prove2.me/submissions/a14f5d78-7164-4f7b-8f49-6e880520ae7d

import Theorems.Thm_Freiman_section14_state_from_records
import Theorems.Thm_Freiman_section14_record_sound
import Definitions.Def_Freiman_section14Geometry
import Mathlib.Tactic.FinCases

open Freiman

theorem solution : ∀ (C : Section14Catalog) (si : ℕ), section14StateValid C si → section14StateSound C si := by
  exact section14_state_from_records section14_record_sound
