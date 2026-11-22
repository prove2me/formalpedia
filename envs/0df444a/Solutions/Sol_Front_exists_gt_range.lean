-- Prove2me | solution 1 for Front.exists_gt_range
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:43:29.753084+00:00
-- url     : https://prove2.me/submissions/3f36424c-e50d-433e-a272-56d347388593

module
public import Definitions.Def_LeanPool_NashWilliams_Combinatorics_Front_Defs
public import Mathlib.SetTheory.Ordinal.Rank
public import Mathlib.Order.Lattice.Nat
public import Definitions.Def_LeanPool_NashWilliams_Combinatorics_Front_Rank

set_option autoImplicit true
@[expose] public section
public section
open Set List Ordinal
universe u
noncomputable section
open Front
variable {F : Set (List ℕ)} {M : ℕ → ℕ}
namespace Front
theorem _root_.solution (hM : StrictMono M) (n : ℕ) : ∃ x ∈ Set.range M, n < x :=
  (Set.infinite_range_of_injective hM.injective).exists_gt n
end Front
