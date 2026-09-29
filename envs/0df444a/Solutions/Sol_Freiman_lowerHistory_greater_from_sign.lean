-- Prove2me | solution 1 for Freiman.lowerHistory_greater_from_sign
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-12T05:49:14.514739+00:00
-- url     : https://prove2.me/submissions/92b6a80e-47bb-4c3f-a11a-d212977ceba6

import Definitions.Def_Freiman_lowerHistoryVerification
import Theorems.Thm_Freiman_lowerHistory_greater_semantics

open Freiman

theorem solution
    (_hsg : ∀ z : CertField, (lowerHistorySign z = 0 ↔ certFieldVal z = 0) ∧
      (0 < lowerHistorySign z ↔ 0 < certFieldVal z))
    (base : LowerPair) (C : LowerHistoryContext)
    (hc : lowerHistoryContextFits base C)
    (x y : CertField × CertField)
    (hx : 0 ≤ certFieldVal x.1 ∧ 0 ≤ certFieldVal x.2)
    (hy : 0 ≤ certFieldVal y.1 ∧ 0 ≤ certFieldVal y.2) :
    lowerHistoryComparisonHolds (lowerHistoryGreater C x y)
      (lowerRatio base.1) (lowerRatio base.2) (lowerScale base) ↔
      lowerHistoryValue base C y ≤ lowerHistoryValue base C x := by
  exact lowerHistory_greater_semantics base C hc x y hx hy
