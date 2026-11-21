-- Prove2me | solution 1 for Champernowne.champBlocks_prefix_champPrefix
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:39:36.491624+00:00
-- url     : https://prove2.me/submissions/f33272cd-d064-4044-98de-30243e35acc5

module
public import Definitions.Def_LeanPool_Champernowne_DigitCount
public import Definitions.Def_LeanPool_Champernowne_Prefix
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Definitions.Def_LeanPool_Champernowne_Positions
public import Theorems.Thm_Champernowne_champPrefix_prefix
public import Theorems.Thm_Champernowne_champBlocks_prefix
public import Theorems.Thm_Champernowne_length_champPrefix


set_option autoImplicit true
@[expose] public section
public section
open Champernowne
namespace Champernowne
theorem _root_.solution {b N n : ℕ}
    (h : (champBlocks b N).length ≤ n) :
    champBlocks b N <+: champPrefix b n := by
  have hNn : N ≤ n := le_trans (le_length_champBlocks b N) h
  exact List.prefix_of_prefix_length_le (champBlocks_prefix hNn)
    (champPrefix_prefix b n) (by rw [length_champPrefix]; exact h)
end Champernowne
