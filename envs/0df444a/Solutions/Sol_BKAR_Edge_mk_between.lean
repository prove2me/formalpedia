-- Prove2me | solution 1 for BKAR.Edge.mk_between
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:02:42.015905+00:00
-- url     : https://prove2.me/submissions/8968e087-6de7-4a9b-bdbe-129aa18f0d93

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
theorem _root_.solution (i j : V) (hij : i ≠ j) : (mk i j hij).Between i j :=
  rfl
end BKAR.Edge
