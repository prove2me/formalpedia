-- Prove2me | solution 1 for Erdos1219.ofFinsetColouring_symm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:43:15.710801+00:00
-- url     : https://prove2.me/submissions/4763b95b-e4f4-4672-8c4e-471657734d2b

import Mathlib.SetTheory.Cardinal.Aleph
import Mathlib.SetTheory.Cardinal.Regular
import Mathlib.SetTheory.Cardinal.Arithmetic
import Mathlib.Data.Finset.Card
import Definitions.Def_Erdos1219_Defs
import Theorems.Thm_Erdos1219_ofFinsetColouring_apply

set_option autoImplicit false
open Cardinal
open Erdos1219
universe u
variable {V : Type u}
namespace Erdos1219
theorem _root_.solution (col : {s : Finset V // s.card = 2} → Bool) (x y : V) :
    ofFinsetColouring col x y = ofFinsetColouring col y x := by
  classical
  by_cases h : x = y
  · subst h; rfl
  · have h' : y ≠ x := fun e => h e.symm
    rw [ofFinsetColouring_apply col h, ofFinsetColouring_apply col h']
    congr 1
    exact Subtype.ext (Finset.pair_comm x y)
end Erdos1219
