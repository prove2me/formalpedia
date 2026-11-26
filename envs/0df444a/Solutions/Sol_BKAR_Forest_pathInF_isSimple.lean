-- Prove2me | solution 1 for BKAR.Forest.pathInF_isSimple
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:02:23.491086+00:00
-- url     : https://prove2.me/submissions/3bebf868-2c8d-4d21-9ee1-bab3ef83313f

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Quotient
import Mathlib.Data.Sym.Sym2
import Definitions.Def_BKAR_Forest

set_option autoImplicit false
open BKAR
open BKAR.Forest
variable {V} [Fintype V] [DecidableEq V]
namespace BKAR.Forest
theorem _root_.solution (F : Forest V) {i j : V}
    (h : F.inSameComponent i j) :
    IsSimplePath F (F.pathInF i j h) i j :=
  F.acyclic.pathIn_isSimple h
end BKAR.Forest
