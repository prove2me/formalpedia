-- Prove2me | solution 1 for FloorRecurrence.floor_child_le_ratio
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.154279+00:00
-- url     : https://prove2.me/submissions/75bf2ac4-9461-4521-aa9a-83a03ba24d20

import Definitions.Def_FloorDepth
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_FloorRecurrence

set_option autoImplicit true
open FloorRecurrence
open scoped BigOperators
namespace FloorRecurrence
theorem _root_.solution (m t e : ℕ) (hm : 0 < m) :
    (FloorDepth.child m t e : ℝ) ≤ ((t : ℝ) / m) * e := by
  have hf : ((e / m : ℕ) : ℝ) * m ≤ e := by exact_mod_cast Nat.div_mul_le_self e m
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hdiv : ((e / m : ℕ) : ℝ) ≤ (e : ℝ) / m := (le_div_iff₀ hmR).mpr hf
  have h := mul_le_mul_of_nonneg_left hdiv (Nat.cast_nonneg t : (0 : ℝ) ≤ t)
  simpa only [FloorDepth.child, Nat.cast_mul, div_mul_eq_mul_div, mul_div_assoc] using h
end FloorRecurrence
