-- Prove2me | solution 1 for BKAR.Forest.inSameComponent_iff_of_edges_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:04:00.835784+00:00
-- url     : https://prove2.me/submissions/22c865b3-86ca-4fa7-8ece-900e08119264

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Quotient
import Mathlib.Data.Sym.Sym2
import Definitions.Def_BKAR_Forest
import Theorems.Thm_BKAR_Forest_inSameComponent_of_edges_eq

set_option autoImplicit false
open BKAR
open BKAR.Forest
variable {V} [Fintype V] [DecidableEq V]
namespace BKAR.Forest
theorem _root_.solution
    (F G : Forest V) (hedges : F.edges = G.edges)
    {i j : V} :
    F.inSameComponent i j ↔ G.inSameComponent i j :=
  ⟨F.inSameComponent_of_edges_eq G hedges,
    G.inSameComponent_of_edges_eq F hedges.symm⟩
end BKAR.Forest
