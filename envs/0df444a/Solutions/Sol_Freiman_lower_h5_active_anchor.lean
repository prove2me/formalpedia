-- Prove2me | solution 1 for Freiman.lower_h5_active_anchor
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T15:06:57.229871+00:00
-- url     : https://prove2.me/submissions/ba7aefb5-e5cf-46f1-990b-d858b23bbcac
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_Freiman_lower_h5_right3_anchor
import Theorems.Thm_Freiman_lower_h5_predecessor_coverage
import Theorems.Thm_Freiman_lower_h5_catalog
import Theorems.Thm_Freiman_lower_guard_offered
import Theorems.Thm_Freiman_lower_h5_initial_exclusion
import Theorems.Thm_Freiman_lower_h5_bindings
import Theorems.Thm_Freiman_lower_h5_reached_premises
import Theorems.Thm_Freiman_lowerHistory_goodness_semantics
import Theorems.Thm_Freiman_lowerHistory_pull_value
import Theorems.Thm_Freiman_lowerHistory_width_threshold
import Theorems.Thm_Freiman_lower_h5_numeric_to_anchor
import Theorems.Thm_Freiman_lowerHistory_endpoint_semantics
import Theorems.Thm_Freiman_lowerHistory_greater_semantics
import Theorems.Thm_Freiman_lower_h5_numerics
import Theorems.Thm_Freiman_lower_h5_exception_event
import Theorems.Thm_Freiman_lower_h5_exception_anchor
import Definitions.Def_Freiman_lowerH5Verification
import Definitions.Def_Freiman_lowerInitialEntry
import Mathlib.Tactic

open Freiman
theorem solution (t : ℝ) (h : ℕ → LowerPair) (n : ℕ) (hh : lowerHistory t h n)
    (ha : lowerH5Active (h n)) : lowerH5LowerBound (h n) t := by
  by_cases hr : lowerEnds (lowerNormalize (h n)).2 [3]
  · exact lower_h5_right3_anchor (h n) t (hh.2.1 n (Nat.le_refl n)) ha hr
  · obtain ⟨c,hc,him⟩ := lower_h5_predecessor_coverage lower_h5_catalog lower_guard_offered lower_h5_initial_exclusion t h n hh ha hr
    have hshape := (lower_h5_bindings c hc).1
    have hsrc := lower_h5_reached_premises lowerHistory_goodness_semantics lowerHistory_pull_value lowerHistory_width_threshold t h n hh ha c hshape him
    rcases lower_h5_numeric_to_anchor lowerHistory_endpoint_semantics lowerHistory_greater_semantics t h n hh ha c hshape him hsrc (lower_h5_numerics c hc) with hb | he
    · exact hb
    · obtain ⟨m,hm⟩ := lower_h5_exception_event t h n hh c hshape him he
      exact lower_h5_exception_anchor t h n m hh hm
