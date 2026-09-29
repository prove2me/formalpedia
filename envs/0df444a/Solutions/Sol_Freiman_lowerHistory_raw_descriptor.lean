-- Prove2me | solution 1 for Freiman.lowerHistory_raw_descriptor
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T13:07:15.730563+00:00
-- url     : https://prove2.me/submissions/a20a3153-909e-419e-9180-126b6498da06

import Definitions.Def_Freiman_lowerHistoryVerification
import Mathlib.Tactic
import Theorems.Thm_Freiman_lowerHistory_marked_side
import Theorems.Thm_Freiman_lowerHistory_initial_descriptor
import Theorems.Thm_Freiman_lowerHistory_generic_descriptor
import Theorems.Thm_Freiman_lower_history_origin_cases
import Theorems.Thm_Freiman_lower_forced_reflections

open Freiman

theorem solution (t : ℝ) (h : ℕ → LowerPair) (n row : ℕ) (hh : lowerHistory t h n)
    (hrow : row ∈ [1,2,3,4]) (haz : lowerHistoryHazard row (h n)) :
    ∃ base p, lowerHistoryStructural p ∧ lowerHistoryReached t h n base p ∧ p.row = row := by
  have hm := lowerHistory_marked_side h n row hrow haz
  rcases lower_history_origin_cases t h n hh (lowerMarkedPhysical h n row) hm with hi | hg
  · exact lowerHistory_initial_descriptor lower_forced_reflections t h n row hh hrow haz hi
  · exact lowerHistory_generic_descriptor lower_forced_reflections t h n row hh hrow haz hg
