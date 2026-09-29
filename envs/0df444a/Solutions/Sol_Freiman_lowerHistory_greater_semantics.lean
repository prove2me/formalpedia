-- Prove2me | solution 1 for Freiman.lowerHistory_greater_semantics
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T13:06:50.187197+00:00
-- url     : https://prove2.me/submissions/88bc7a61-2392-4f81-975a-4bbf35cd3a84

import Definitions.Def_Freiman_lowerHistoryVerification
import Mathlib.Tactic
import Theorems.Thm_Freiman_lowerHistory_greater_from_sign
import Theorems.Thm_Freiman_lowerHistory_sign_value

open Freiman

theorem solution (base : LowerPair) (C : LowerHistoryContext) (hc : lowerHistoryContextFits base C)
    (x y : CertField × CertField) (hx : 0 ≤ certFieldVal x.1 ∧ 0 ≤ certFieldVal x.2)
    (hy : 0 ≤ certFieldVal y.1 ∧ 0 ≤ certFieldVal y.2) :
    lowerHistoryComparisonHolds (lowerHistoryGreater C x y) (lowerRatio base.1) (lowerRatio base.2) (lowerScale base) ↔
      lowerHistoryValue base C y ≤ lowerHistoryValue base C x := by
  exact lowerHistory_greater_from_sign lowerHistory_sign_value base C hc x y hx hy
