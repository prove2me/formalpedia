-- Prove2me | solution 1 for ErdosProblems.MulticolourTriangleRamsey.choose_le_choose_of_le_half
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:50.335123+00:00
-- url     : https://prove2.me/submissions/c08f8eb4-a750-4f10-b9a1-d67b055c9dbe

import Mathlib
import Definitions.Def_MulticolorTriangleRamsey

set_option autoImplicit true
open ErdosProblems ErdosProblems.MulticolourTriangleRamsey
open Filter Finset SimpleGraph
open scoped Topology
namespace ErdosProblems.MulticolourTriangleRamsey
theorem _root_.solution {N d s : ℕ}
    (hds : d ≤ s) (hhalf : 2 * s ≤ N) :
    N.choose d ≤ N.choose s := by
  induction hds with
  | refl => exact le_rfl
  | @step d hds ih =>
      have hprevious : 2 * d ≤ N := by omega
      exact (ih hprevious).trans
        (Nat.choose_le_succ_of_lt_half_left (by omega))
end ErdosProblems.MulticolourTriangleRamsey
