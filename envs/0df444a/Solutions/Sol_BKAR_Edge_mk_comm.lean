-- Prove2me | solution 1 for BKAR.Edge.mk_comm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:03:35.106827+00:00
-- url     : https://prove2.me/submissions/2d94ffbf-bbec-4639-9631-89083492522a

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Quotient
import Mathlib.Data.Sym.Sym2
import Definitions.Def_BKAR_Forest

set_option autoImplicit false
open BKAR
open BKAR.Edge
variable {V} [DecidableEq V]
namespace BKAR.Edge
theorem _root_.solution (i j : V) (hij : i ≠ j) :
    mk i j hij = mk j i hij.symm := by
  apply Subtype.ext
  exact Sym2.eq_swap
end BKAR.Edge
