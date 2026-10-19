-- Prove2me | solution 1 for ErdosProblems.MulticolourTriangleRamsey.paletteLogWidth_le_two_log
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:50.335123+00:00
-- url     : https://prove2.me/submissions/99c2b784-fcc5-4112-ad74-7fb1310c509a

import Mathlib
import Definitions.Def_MulticolorTriangleRamsey
import Theorems.Thm_ErdosProblems_MulticolourTriangleRamsey_one_le_log_nat_of_three_le

set_option autoImplicit true
open ErdosProblems ErdosProblems.MulticolourTriangleRamsey
open Filter Finset SimpleGraph
open scoped Topology
namespace ErdosProblems.MulticolourTriangleRamsey
theorem _root_.solution (H : ℕ) (hH : 3 ≤ H) :
    (paletteLogWidth H : ℝ) ≤ 2 * Real.log (H : ℝ) := by
  have hlog : 1 ≤ Real.log (H : ℝ) :=
    one_le_log_nat_of_three_le H hH
  have hceil :
      (⌈Real.log (H : ℝ)⌉₊ : ℝ) ≤ Real.log (H : ℝ) + 1 :=
    (Nat.ceil_lt_add_one (by linarith : 0 ≤ Real.log (H : ℝ))).le
  unfold paletteLogWidth
  by_cases htwo : 2 ≤ ⌈Real.log (H : ℝ)⌉₊
  · rw [max_eq_right htwo]
    linarith
  · rw [max_eq_left (by omega)]
    norm_num
    linarith
end ErdosProblems.MulticolourTriangleRamsey
