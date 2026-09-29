-- Prove2me | solution 2 for Freiman.lowerHistory_source_premises
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-11T08:06:53.164978+00:00
-- url     : https://prove2.me/submissions/48f997d9-cd9c-4810-80e6-121498d7b8e1

import Definitions.Def_Freiman_lowerHistoryVerification
import Mathlib.Tactic
import Theorems.Thm_Freiman_lowerHistory_source_events
import Theorems.Thm_Freiman_lowerHistory_source_dnf_induction

open Freiman

-- `lowerHistory_source_dnf_induction` derives the source-premise disjunction from the
-- event package `LowerHistorySourceEvents base p`; `lowerHistory_source_events` supplies
-- exactly that package from the history/reached/hazard hypotheses.
theorem solution (t : ℝ) (h : ℕ → LowerPair) (n : ℕ) (hh : lowerHistory t h n)
    (base : LowerPair) (p : LowerHistoryPath) (hp : lowerHistoryStructural p)
    (hr : lowerHistoryReached t h n base p) (haz : lowerHistoryHazard p.row (h n)) :
    ∃ bs ∈ lowerHistorySourcePremises p, lowerHistoryAtBase base bs :=
  lowerHistory_source_dnf_induction base p hp
    (lowerHistory_source_events t h n hh base p hp hr haz)
