-- Prove2me | solution 1 for Champernowne.length_champBlocks_champIndex_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:38:23.467062+00:00
-- url     : https://prove2.me/submissions/52660660-5e96-42e1-a8c2-e767a1b682b2

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
    (champBlocks b (champIndex b n)).length ≤ n := by
  have h0 : (champBlocks b 0).length ≤ n := by simp [champBlocks]
  exact Nat.findGreatest_spec (P := fun N => (champBlocks b N).length ≤ n)
    (Nat.zero_le n) h0
end Champernowne
