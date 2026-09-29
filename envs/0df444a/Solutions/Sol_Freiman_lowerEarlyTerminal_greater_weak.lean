-- Prove2me | solution 1 for Freiman.lowerEarlyTerminal_greater_weak
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T15:05:08.24212+00:00
-- url     : https://prove2.me/submissions/81672b2b-47a4-466c-837d-85ec97b93ea3

import Definitions.Def_Freiman_lowerEarlyTerminalGeometry


import Theorems.Thm_Freiman_lowerHistory_greater_semantics

open Freiman

theorem solution (base : LowerPair) (C : LowerHistoryContext) (hc : C.parity = (false,false))
    (hf : lowerHistoryContextFits base C) (x y : CertField × CertField)
    (hx : 0 ≤ certFieldVal x.1 ∧ 0 ≤ certFieldVal x.2)
    (hy : 0 ≤ certFieldVal y.1 ∧ 0 ≤ certFieldVal y.2) : section14ComparisonHolds (lowerEarlyTerminalGreater x y false)
      (lowerRatio base.1) (lowerRatio base.2) (lowerScale base) ↔
        lowerHistoryValue base C y ≤ lowerHistoryValue base C x := by
  have h := lowerHistory_greater_semantics base C hf x y hx hy
  by_cases h1 : 0 ≤ lowerHistorySign (certFieldSub x.1 y.1) ∧ 0 ≤ lowerHistorySign (certFieldSub x.2 y.2) <;>
    by_cases h2 : lowerHistorySign (certFieldSub x.1 y.1) ≤ 0 ∧ lowerHistorySign (certFieldSub x.2 y.2) ≤ 0 <;>
      simpa [lowerEarlyTerminalGreater,lowerHistoryGreater,lowerHistoryComparisonHolds,
        section14ComparisonHolds,hc,h1,h2] using h
