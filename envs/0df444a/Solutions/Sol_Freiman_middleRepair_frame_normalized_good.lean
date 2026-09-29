-- Prove2me | solution 1 for Freiman.middleRepair_frame_normalized_good
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T15:26:49.726966+00:00
-- url     : https://prove2.me/submissions/a8920dac-40c0-4bb0-aba3-c04f2c4e3da9

import Theorems.Thm_Freiman_middleRepair_frame_child_normalized
import Mathlib.Tactic

open Freiman

theorem solution :
  ∀ c : MiddleCore, middleRepairGood (middleNormalized c) ↔ middleRepairGood c := by
  intro c
  simp only [middleRepairGood, middleRepair_frame_child_normalized]
