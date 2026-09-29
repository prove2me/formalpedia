-- Prove2me | solution 1 for Freiman.middle_normalization_domain
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T22:50:03.706424+00:00
-- url     : https://prove2.me/submissions/6f25638c-8ce5-473b-922a-2a87c5e11f9f

import Definitions.Def_Freiman_middleRepair
import Mathlib.Tactic.SplitIfs

open Freiman

theorem solution :
    ∀ c : MiddleCore, middleRegular c →
      middleRegular (middleNormalized c) ∧
      middleWidth (middleNormalized c).right ≤ middleWidth (middleNormalized c).left := by
  intro c hc
  unfold middleNormalized
  split_ifs with h
  · exact ⟨hc, h⟩
  · rcases hc with ⟨hl, hr, hwl, hwr⟩
    exact ⟨⟨hr, hl, hwr, hwl⟩, le_of_lt (lt_of_not_ge h)⟩

#print axioms solution
