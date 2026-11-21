-- Prove2me | solution 1 for Champernowne.n_lt_length_champIndex_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:40:12.529262+00:00
-- url     : https://prove2.me/submissions/5a8c5665-087e-4b62-9cf3-5578600dfaae

module
public import Definitions.Def_LeanPool_Champernowne_DigitCount
public import Definitions.Def_LeanPool_Champernowne_Prefix
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Definitions.Def_LeanPool_Champernowne_Positions
public import Theorems.Thm_Champernowne_lt_length_champBlocks_champIndex_succ

set_option autoImplicit true
@[expose] public section
public section
open Champernowne
namespace Champernowne
theorem _root_.solution (b n : ℕ) :
    n < (champBlocks b (champIndex b n)).length
      + (bigDigits b (champIndex b n + 1)).length := by
  have h := lt_length_champBlocks_champIndex_succ b n
  rwa [champBlocks_succ, List.length_append] at h
end Champernowne
