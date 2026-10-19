-- Prove2me | solution 1 for ErdosProblems.MulticolourTriangleRamsey.missing_symbol_power_bound_nat
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:50.335123+00:00
-- url     : https://prove2.me/submissions/0a7ad3fa-d99a-47af-b7ba-b78de160aea2

import Mathlib
import Definitions.Def_MulticolorTriangleRamsey
import Theorems.Thm_ErdosProblems_MulticolourTriangleRamsey_missing_symbol_power_bound

set_option autoImplicit true
open ErdosProblems ErdosProblems.MulticolourTriangleRamsey
open Filter Finset SimpleGraph
open scoped Topology
namespace ErdosProblems.MulticolourTriangleRamsey
theorem _root_.solution (H m : ℕ) (hH : 2 ≤ H)
    (hm : 2 * (H : ℝ) * Real.log (H : ℝ) ≤ (m : ℝ)) :
    H ^ 2 * (H - 1) ^ (m + 1) < H ^ (m + 1) := by
  have hreal := missing_symbol_power_bound H m hH hm
  have hcast :
      ((H ^ 2 * (H - 1) ^ (m + 1) : ℕ) : ℝ) <
        ((H ^ (m + 1) : ℕ) : ℝ) := by
    simpa [Nat.cast_sub (show 1 ≤ H by omega)] using hreal
  exact_mod_cast hcast
end ErdosProblems.MulticolourTriangleRamsey
