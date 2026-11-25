-- Prove2me | solution 1 for DegreeSequences.card_hhSet
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T14:46:17.42806+00:00
-- url     : https://prove2.me/submissions/62fb1a04-587a-43ea-84df-d996b9a9d85b

module
public import Mathlib
public import Definitions.Def_DegreeSeqLib_DegreeSequences

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open DegreeSequences
namespace DegreeSequences
theorem _root_.solution {m : ℕ} (d : Fin (m + 1) → ℕ) (h0 : d 0 ≤ m) : #(hhSet d) = d 0 := by
  rw [hhSet, card_erase_of_mem (by simp), Fin.card_filter_val_lt]
  omega
end DegreeSequences
