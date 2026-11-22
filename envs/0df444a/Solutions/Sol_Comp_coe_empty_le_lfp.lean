-- Prove2me | solution 1 for Comp.coe_empty_le_lfp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T23:27:24.366998+00:00
-- url     : https://prove2.me/submissions/1231a69d-31b1-4620-a784-6c55554c43cf

import Definitions.Def_Comp_Lattice
import Mathlib.Data.Fintype.Card
import Definitions.Def_Comp_FixLoop

set_option autoImplicit true
open Comp
variable {S : Type*} [DecidableEq S]
variable [Fintype S]
omit [Fintype S] [DecidableEq S]
namespace Comp
theorem _root_.solution (F : Set S →o Set S) : (↑(∅ : Finset S) : Set S) ≤ F.lfp := by
  rw [Finset.coe_empty]
  exact bot_le
end Comp
