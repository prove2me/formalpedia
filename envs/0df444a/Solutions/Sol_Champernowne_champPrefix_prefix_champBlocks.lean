-- Prove2me | solution 1 for Champernowne.champPrefix_prefix_champBlocks
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:40:23.470407+00:00
-- url     : https://prove2.me/submissions/1654d69e-7a66-44bf-85d4-0b3ecee2c1fe

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
theorem _root_.solution {b n N : ℕ}
    (h : n ≤ (champBlocks b N).length) :
    champPrefix b n <+: champBlocks b N := by
  rcases le_total n N with hnN | hNn
  · exact (champPrefix_prefix b n).trans (champBlocks_prefix hnN)
  · exact List.prefix_of_prefix_length_le (champPrefix_prefix b n)
      (champBlocks_prefix hNn) (by rw [length_champPrefix]; exact h)
end Champernowne
