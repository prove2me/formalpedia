-- Prove2me | solution 1 for Front.shrink_eq_shrinkOn_range
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:43:51.367583+00:00
-- url     : https://prove2.me/submissions/c8fbe1cf-c16c-4ab1-ab4b-2a96279c8172

module
public import Definitions.Def_LeanPool_NashWilliams_Combinatorics_Front_Rank
public import Definitions.Def_LeanPool_NashWilliams_Combinatorics_Front_Shrink

set_option autoImplicit true
@[expose] public section
public section
open Set List
noncomputable section
open Front
variable {F : Set (List ℕ)} {M : ℕ → ℕ}
namespace Front
theorem _root_.solution (F : Set (List ℕ)) (N : ℕ → ℕ) :
    shrink F N = shrinkOn F (Set.range N) := rfl
end Front
