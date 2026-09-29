-- Prove2me | solution 1 for Freiman.lowerHistory_source_events
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T13:07:02.923681+00:00
-- url     : https://prove2.me/submissions/967461f1-ebb9-4f76-b669-9476061c15fc

import Definitions.Def_Freiman_lowerHistoryVerification
import Mathlib.Tactic
import Theorems.Thm_Freiman_lowerHistory_reached_base
import Theorems.Thm_Freiman_lowerHistory_reached_goodness
import Theorems.Thm_Freiman_lowerHistory_reached_choices
import Theorems.Thm_Freiman_lowerHistory_reached_normalizations
import Theorems.Thm_Freiman_lowerHistory_reached_final
import Theorems.Thm_Freiman_lowerHistory_goodness_semantics
import Theorems.Thm_Freiman_lowerHistory_pull_value
import Theorems.Thm_Freiman_lowerHistory_source_choices
import Theorems.Thm_Freiman_lowerHistory_width_threshold
import Theorems.Thm_Freiman_lower_forced_reflections
import Theorems.Thm_Freiman_lower_entry_family_domain

open Freiman

theorem solution (t : ℝ) (h : ℕ → LowerPair) (n : ℕ) (hh : lowerHistory t h n)
    (base : LowerPair) (p : LowerHistoryPath) (hp : lowerHistoryStructural p) (hr : lowerHistoryReached t h n base p) (haz : lowerHistoryHazard p.row (h n)) :
    LowerHistorySourceEvents base p := by
  exact ⟨lowerHistory_reached_base lower_entry_family_domain lowerHistory_goodness_semantics t h n hh base p hp hr,
    lowerHistory_reached_goodness lowerHistory_goodness_semantics lowerHistory_pull_value t h n hh base p hp hr,
    lowerHistory_reached_choices lowerHistory_source_choices lowerHistory_pull_value t h n hh base p hp hr,
    lowerHistory_reached_normalizations lower_forced_reflections lowerHistory_width_threshold t h n hh base p hp hr,
    lowerHistory_reached_final lowerHistory_pull_value t h n hh base p hp hr haz⟩
