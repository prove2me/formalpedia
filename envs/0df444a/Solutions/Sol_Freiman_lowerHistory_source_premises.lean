-- Prove2me | solution 1 for Freiman.lowerHistory_source_premises
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T13:07:02.844615+00:00
-- url     : https://prove2.me/submissions/38e24518-7649-4bd1-998d-671cdc80d872

import Definitions.Def_Freiman_lowerHistoryVerification
import Mathlib.Tactic
import Theorems.Thm_Freiman_lowerHistory_source_dnf_induction
import Theorems.Thm_Freiman_lowerHistory_source_events

open Freiman

theorem solution (t : ℝ) (h : ℕ → LowerPair) (n : ℕ) (hh : lowerHistory t h n)
    (base : LowerPair) (p : LowerHistoryPath) (hp : lowerHistoryStructural p) (hr : lowerHistoryReached t h n base p) (haz : lowerHistoryHazard p.row (h n)) :
    ∃ bs ∈ lowerHistorySourcePremises p, lowerHistoryAtBase base bs := by
  exact lowerHistory_source_dnf_induction base p hp (lowerHistory_source_events t h n hh base p hp hr haz)
