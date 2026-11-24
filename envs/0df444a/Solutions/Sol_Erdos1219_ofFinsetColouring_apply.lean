-- Prove2me | solution 1 for Erdos1219.ofFinsetColouring_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:40:04.469092+00:00
-- url     : https://prove2.me/submissions/7a00ada1-3d16-4449-8688-1551f948d04b

import Mathlib.SetTheory.Cardinal.Aleph
import Mathlib.SetTheory.Cardinal.Regular
import Mathlib.SetTheory.Cardinal.Arithmetic
import Mathlib.Data.Finset.Card
import Definitions.Def_Erdos1219_Defs

set_option autoImplicit false
open Cardinal
open Erdos1219
universe u
variable {V : Type u}
namespace Erdos1219
theorem _root_.solution [DecidableEq V] (col : {s : Finset V // s.card = 2} → Bool)
    {x y : V} (h : x ≠ y) :
    ofFinsetColouring col x y = col ⟨{x, y}, Finset.card_pair h⟩ := by
  unfold ofFinsetColouring
  simp only [h, ↓reduceDIte]
  congr
  exact Subsingleton.elim _ _
end Erdos1219
