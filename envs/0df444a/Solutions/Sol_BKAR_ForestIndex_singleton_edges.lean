-- Prove2me | solution 1 for BKAR.ForestIndex.singleton_edges
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:04:11.873835+00:00
-- url     : https://prove2.me/submissions/b1f7deb5-2a0c-4994-a207-2f339a72b3c8

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Quotient
import Mathlib.Data.Sym.Sym2
import Definitions.Def_BKAR_Forest

set_option autoImplicit false
open BKAR
open BKAR.ForestIndex
variable {V} [Fintype V] [DecidableEq V]
namespace BKAR.ForestIndex
theorem _root_.solution (e : Edge V) :
    (singleton e : ForestIndex V).edges = {e} :=
  rfl
end BKAR.ForestIndex
