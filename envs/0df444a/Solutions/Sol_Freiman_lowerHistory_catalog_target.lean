-- Prove2me | solution 1 for Freiman.lowerHistory_catalog_target
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T13:07:28.434277+00:00
-- url     : https://prove2.me/submissions/ce6b3183-f472-471a-8ac6-db920a22ce95

import Definitions.Def_Freiman_lowerHistoryVerification
import Mathlib.Tactic
import Theorems.Thm_Freiman_lowerHistory_source_premises
import Theorems.Thm_Freiman_lowerHistory_reached_rectangle
import Theorems.Thm_Freiman_lowerHistory_path_soundness
import Theorems.Thm_Freiman_lowerHistory_all_bindings
import Theorems.Thm_Freiman_lowerHistory_all_witnesses
import Theorems.Thm_Freiman_lowerHistory_earlier_anchor
import Theorems.Thm_Freiman_lowerHistory_comparison_transfer
import Theorems.Thm_Freiman_lowerHistory_endpoint_semantics
import Theorems.Thm_Freiman_lowerHistory_survivor_target
import Theorems.Thm_Freiman_lowerHistory_greater_semantics
import Theorems.Thm_Freiman_lower_entry_family_domain

open Freiman

theorem solution (t : ℝ) (h : ℕ → LowerPair) (n : ℕ) (hh : lowerHistory t h n)
    (base : LowerPair) (p : LowerHistoryPath) (hp : lowerHistoryStructural p) (hr : lowerHistoryReached t h n base p) (hmem : p ∈ lowerHistoryPaths.toList) (haz : lowerHistoryHazard p.row (h n)) :
    lowerHistoryTarget p.row (h n) t := by
  have hs := lowerHistory_source_premises t h n hh base p hp hr haz
  have hm := lowerHistory_reached_rectangle lower_entry_family_domain t h n hh base p hmem hp hr
  rcases lowerHistory_path_soundness p hmem lowerHistory_all_bindings lowerHistory_all_witnesses
    (lowerRatio base.1) (lowerRatio base.2) (lowerScale base) hm hs with hi | hg
  · exact lowerHistory_survivor_target t h n hh base p hp hr hi.2
  · exact lowerHistory_comparison_transfer lowerHistory_greater_semantics lowerHistory_endpoint_semantics t h n hh base p hp hr
      hg.1 hg.2.1 (lowerHistory_earlier_anchor t h n hh base p hp hr hg.1) hg.2.2
