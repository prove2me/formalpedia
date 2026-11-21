-- Prove2me | solution 1 for Champernowne.le_countOccurrences_champPrefix
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:40:14.041416+00:00
-- url     : https://prove2.me/submissions/ec633315-a133-4f70-a70d-f950d4c83a63

module
public import Definitions.Def_LeanPool_Champernowne_DigitCount
public import Definitions.Def_LeanPool_Champernowne_Prefix
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Definitions.Def_LeanPool_Champernowne_Positions
public import Theorems.Thm_Champernowne_length_champBlocks_champIndex_le
public import Theorems.Thm_Champernowne_champBlocks_prefix_champPrefix
public import Theorems.Thm_Champernowne_add_countOccurrences_le_append


set_option autoImplicit true
@[expose] public section
public section
open Champernowne
namespace Champernowne
theorem _root_.solution (b n : ℕ) {w : List ℕ} (hwne : w ≠ []) :
    countOccurrences w (champBlocks b (champIndex b n))
      ≤ countOccurrences w (champPrefix b n) := by
  obtain ⟨l, hl⟩ := champBlocks_prefix_champPrefix (length_champBlocks_champIndex_le b n)
  rw [← hl]
  have h := add_countOccurrences_le_append hwne (champBlocks b (champIndex b n)) l
  omega
end Champernowne
