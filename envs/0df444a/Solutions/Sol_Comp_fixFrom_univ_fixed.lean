-- Prove2me | solution 1 for Comp.fixFrom_univ_fixed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T23:29:55.936436+00:00
-- url     : https://prove2.me/submissions/4926a014-e06c-41a9-a802-c46b61702bfb

import Definitions.Def_Comp_Lattice
import Mathlib.Data.Fintype.Card
import Definitions.Def_Comp_FixLoop
import Theorems.Thm_Comp_fixAux_fixed_of_card_le

set_option autoImplicit true
open Comp
variable {S : Type*} [DecidableEq S]
variable [Fintype S]
namespace Comp
theorem _root_.solution (f : Finset S → Finset S) (hmono : Monotone f) :
    f (fixFrom f Finset.univ) = fixFrom f Finset.univ :=
  fixAux_fixed_of_card_le f hmono _ _ (Finset.subset_univ _) (le_of_eq Finset.card_univ)
end Comp
