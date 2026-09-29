-- Prove2me | solution 1 for Freiman.lowerHistory_reached_final
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-12T05:58:23.902197+00:00
-- url     : https://prove2.me/submissions/b576a02e-7f56-45c7-80d1-8d0023720a97

import Definitions.Def_Freiman_lowerHistoryVerification
import Theorems.Thm_Freiman_lowerHistory_source_events

open Freiman

theorem solution
    (_hpull : LowerHistoryPullLaw)
    (t : ℝ) (h : ℕ → LowerPair) (n : ℕ)
    (hh : lowerHistory t h n)
    (base : LowerPair) (p : LowerHistoryPath)
    (hp : lowerHistoryStructural p)
    (hr : lowerHistoryReached t h n base p)
    (haz : lowerHistoryHazard p.row (h n)) :
    lowerHistoryFinalEvent base p := by
  exact (lowerHistory_source_events t h n hh base p hp hr haz).finalEvent
