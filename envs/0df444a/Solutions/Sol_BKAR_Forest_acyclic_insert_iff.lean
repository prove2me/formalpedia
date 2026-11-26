-- Prove2me | solution 1 for BKAR.Forest.acyclic_insert_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:03:20.609674+00:00
-- url     : https://prove2.me/submissions/8057c97c-f588-44a0-a975-405b5f5ee237

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
theorem _root_.solution (F : Forest V) {i j : V} (hij : i ≠ j)
    (he : Edge.mk i j hij ∉ F.edges) :
    IsAcyclicEdgeSet (insert (Edge.mk i j hij) F.edges) ↔
      ¬ F.inSameComponent i j :=
  show IsAcyclicEdgeSet (insert (Edge.mk i j hij) F.edges) ↔
      ¬ F.acyclic.inSameComponent i j from
    F.acyclic_insert_iff' (i := i) (j := j) hij he
end BKAR.Forest
