-- Prove2me | solution 1 for Freiman.middleRepair_reflect_act_localValue
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T15:26:32.395041+00:00
-- url     : https://prove2.me/submissions/d0efb478-3aa1-4e1c-a4ed-eab0734ce28d

import Theorems.Thm_Freiman_middleRepair_reflect_localValue
import Mathlib.Tactic

open Freiman

theorem solution :
  ∀ (b : Bool) (a : ℤ → ℕ+), localValue (middleRepairActDigits b a) 0 = localValue a 0 := by
  intro b a
  cases b with
  | false => rfl
  | true => exact middleRepair_reflect_localValue a
