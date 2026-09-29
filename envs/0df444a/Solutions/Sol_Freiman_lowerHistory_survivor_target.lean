-- Prove2me | solution 1 for Freiman.lowerHistory_survivor_target
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T13:07:15.201115+00:00
-- url     : https://prove2.me/submissions/f4096c91-8700-4241-83c8-dac2380183dd

import Definitions.Def_Freiman_lowerHistoryVerification
import Mathlib.Tactic
import Theorems.Thm_Freiman_lowerHistory_survivor_family
import Theorems.Thm_Freiman_lower_initial_survivor_target

open Freiman

theorem solution (t : ℝ) (h : ℕ → LowerPair) (n : ℕ) (hh : lowerHistory t h n)
    (base : LowerPair) (p : LowerHistoryPath) (hp : lowerHistoryStructural p) (hr : lowerHistoryReached t h n base p) (hs : lowerHistorySurvivor p) :
    lowerHistoryTarget p.row (h n) t := by
  obtain ⟨f,a,k,v,hm,hb,hn⟩ := lowerHistory_survivor_family t h n hh base p hp hr hs
  have ht := lower_initial_survivor_target t f a k v hm hb (h n) hn
  simpa [lowerHistoryTarget, hs.2.2.1] using ht
