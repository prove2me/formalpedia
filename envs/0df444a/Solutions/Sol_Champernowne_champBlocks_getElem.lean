-- Prove2me | solution 1 for Champernowne.champBlocks_getElem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:39:35.590207+00:00
-- url     : https://prove2.me/submissions/d29d81ad-70fc-4f23-beef-64c5a89fe436

module
public import Definitions.Def_LeanPool_Champernowne_Defs
public import Definitions.Def_LeanPool_Champernowne_Prefix
public import Theorems.Thm_Champernowne_champBlocks_prefix

set_option autoImplicit true
@[expose] public section
public section
open Champernowne
namespace Champernowne
theorem _root_.solution (b N i : ℕ) (h : i < (champBlocks b N).length) :
    (champBlocks b N)[i] = champDigit b i := by
  simp only [champDigit]
  rcases le_total N (i + 1) with hN | hN
  · exact (champBlocks_prefix hN).getElem h
  · exact ((champBlocks_prefix hN).getElem (lt_of_lt_of_le (Nat.lt_succ_self i)
      (le_length_champBlocks b (i + 1)))).symm
end Champernowne
