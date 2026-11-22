-- Prove2me | solution 1 for Comp.fixFrom_empty_fixed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T23:30:04.47096+00:00
-- url     : https://prove2.me/submissions/88fb2502-0480-47b6-b0e0-4e0d18554f7c

import Definitions.Def_Comp_Lattice
import Mathlib.Data.Fintype.Card
import Definitions.Def_Comp_FixLoop
import Theorems.Thm_Comp_fixAux_zero
import Theorems.Thm_Comp_fixAux_fixed_of_compl_card_le
attribute [local simp] Comp.fixAux_zero

set_option autoImplicit true
open Comp
variable {S : Type*} [DecidableEq S]
variable [Fintype S]
namespace Comp
theorem _root_.solution (f : Finset S → Finset S) (hmono : Monotone f) :
    f (fixFrom f ∅) = fixFrom f ∅ :=
  fixAux_fixed_of_compl_card_le f hmono _ _ (Finset.empty_subset _) (by simp)
end Comp
