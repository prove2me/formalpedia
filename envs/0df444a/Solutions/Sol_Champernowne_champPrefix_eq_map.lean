-- Prove2me | solution 1 for Champernowne.champPrefix_eq_map
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:40:12.043323+00:00
-- url     : https://prove2.me/submissions/a740b088-a1a8-47a5-8f35-357d0ac32b79

module
public import Definitions.Def_LeanPool_Champernowne_Defs
public import Definitions.Def_LeanPool_Champernowne_Prefix
public import Theorems.Thm_Champernowne_champBlocks_getElem
public import Theorems.Thm_Champernowne_length_champPrefix

set_option autoImplicit true
@[expose] public section
public section
open Champernowne
namespace Champernowne
theorem _root_.solution (b n : ℕ) :
    champPrefix b n = (List.range n).map (champDigit b) := by
  have hlen := length_champPrefix b n
  apply List.ext_getElem
  · rw [hlen, List.length_map, List.length_range]
  · intro i h1 h2
    have hi : i < (champBlocks b n).length := by
      rw [hlen] at h1
      exact lt_of_lt_of_le h1 (le_length_champBlocks b n)
    simp only [champPrefix, List.getElem_take, List.getElem_map, List.getElem_range]
    exact champBlocks_getElem b n i hi
end Champernowne
