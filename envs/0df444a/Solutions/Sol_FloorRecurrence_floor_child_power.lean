-- Prove2me | solution 1 for FloorRecurrence.floor_child_power
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.154279+00:00
-- url     : https://prove2.me/submissions/30ee11f3-1d19-45ca-abb4-b4912d98e057

import Definitions.Def_FloorDepth
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_FloorRecurrence
import Theorems.Thm_FloorRecurrence_floor_child_le_ratio

set_option autoImplicit true
open FloorRecurrence
open scoped BigOperators
namespace FloorRecurrence
theorem _root_.solution (m t e : ℕ) (p : ℝ) (hm : 0 < m) (hp : 0 ≤ p) :
    (FloorDepth.child m t e : ℝ) ^ p ≤ ((t : ℝ) / m) ^ p * (e : ℝ) ^ p := by
  have h := Real.rpow_le_rpow (Nat.cast_nonneg _) (floor_child_le_ratio m t e hm) hp
  simpa only [Real.mul_rpow (div_nonneg (Nat.cast_nonneg t) (Nat.cast_nonneg m))
    (Nat.cast_nonneg e)] using h
end FloorRecurrence
