-- Prove2me | solution 1 for Freiman.middle_j_orientation
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T15:04:05.062944+00:00
-- url     : https://prove2.me/submissions/9a90a869-8a8b-4f88-a1a7-41ce6e2639b4

import Theorems.Thm_Freiman_middleRepair_j_ratio_specialization
import Theorems.Thm_Freiman_middle_j_real_ratio_bounds
import Definitions.Def_Freiman_middleRepair

open Freiman

theorem solution :
    ∀ (c : MiddleCore) (r : MiddleRow) (k : ℕ), middleRegular c → middleRowCondition c r → middleEssentialJ r = true → 1 ≤ k → 1 < middleWidth ((middleNormalized c).left ++ List.replicate k 3) / middleWidth ((middleNormalized c).right ++ List.replicate k 3) := by
  intro c r k hc hr hj hk
  exact (middleRepair_j_ratio_specialization middle_j_real_ratio_bounds c r k hc hr hj hk).1
