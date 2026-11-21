-- Prove2me | solution 1 for Champernowne.length_champPrefix
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:35:30.88078+00:00
-- url     : https://prove2.me/submissions/cdda9e22-432f-4cfc-99bb-204464ee4aca

module
public import Definitions.Def_LeanPool_Champernowne_Defs
public import Definitions.Def_LeanPool_Champernowne_Prefix

set_option autoImplicit true
@[expose] public section
public section
open Champernowne
namespace Champernowne
theorem _root_.solution (b n : ℕ) : (champPrefix b n).length = n := by
  rw [champPrefix, List.length_take]
  exact Nat.min_eq_left (le_length_champBlocks b n)
end Champernowne
