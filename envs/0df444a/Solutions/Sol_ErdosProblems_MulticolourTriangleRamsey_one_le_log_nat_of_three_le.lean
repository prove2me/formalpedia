-- Prove2me | solution 1 for ErdosProblems.MulticolourTriangleRamsey.one_le_log_nat_of_three_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:50.335123+00:00
-- url     : https://prove2.me/submissions/02e3d7d6-86da-4da1-9fd4-b08897a383a5

import Mathlib
import Definitions.Def_MulticolorTriangleRamsey

set_option autoImplicit true
open ErdosProblems ErdosProblems.MulticolourTriangleRamsey
open Filter Finset SimpleGraph
open scoped Topology
namespace ErdosProblems.MulticolourTriangleRamsey
theorem _root_.solution (H : ℕ) (hH : 3 ≤ H) :
    1 ≤ Real.log (H : ℝ) := by
  have hpos : (0 : ℝ) < H := by exact_mod_cast (by omega : 0 < H)
  apply (Real.le_log_iff_exp_le hpos).mpr
  calc
    Real.exp 1 ≤ (3 : ℝ) := Real.exp_one_lt_three.le
    _ ≤ (H : ℝ) := by exact_mod_cast hH
end ErdosProblems.MulticolourTriangleRamsey
