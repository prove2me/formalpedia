-- Prove2me | solution 1 for FairSelling.mem_TPSset_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:26:34.230321+00:00
-- url     : https://prove2.me/submissions/9ffdec1d-0e22-4dfe-a6aa-381f1eeff6a0

import Mathlib
import Definitions.Def_RequestProject_Selling

set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]
variable {n : ℕ}
omit [DecidableEq G]
namespace FairSelling
theorem _root_.solution (v p : G → ℝ) (hp : ∀ g, 0 ≤ p g) :
    (0 : ℝ) ∈ TPSset n v p := by
  exact Set.mem_setOf_eq.mpr ( div_nonneg ( Finset.sum_nonneg fun _ _ => le_max_of_le_left ( hp _ ) ) ( Nat.cast_nonneg _ ) )
end FairSelling
