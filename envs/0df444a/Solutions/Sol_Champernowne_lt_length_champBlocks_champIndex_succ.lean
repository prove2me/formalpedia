-- Prove2me | solution 1 for Champernowne.lt_length_champBlocks_champIndex_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:39:36.060499+00:00
-- url     : https://prove2.me/submissions/afb0a5bd-c520-44da-b85d-b0f3b60f9848

module
public import Definitions.Def_LeanPool_Champernowne_DigitCount
public import Definitions.Def_LeanPool_Champernowne_Prefix
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Definitions.Def_LeanPool_Champernowne_Positions

set_option autoImplicit true
@[expose] public section
public section
open Champernowne
namespace Champernowne
theorem _root_.solution (b n : ℕ) :
    n < (champBlocks b (champIndex b n + 1)).length := by
  rcases Nat.lt_or_ge n (champIndex b n + 1) with h | h
  · exact lt_of_lt_of_le h (le_length_champBlocks b _)
  · have hng := Nat.findGreatest_is_greatest
      (P := fun N => (champBlocks b N).length ≤ n)
      (k := champIndex b n + 1) (Nat.lt_succ_self _) h
    exact Nat.lt_of_not_le hng
end Champernowne
