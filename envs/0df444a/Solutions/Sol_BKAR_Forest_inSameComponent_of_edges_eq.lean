-- Prove2me | solution 1 for BKAR.Forest.inSameComponent_of_edges_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:03:14.462572+00:00
-- url     : https://prove2.me/submissions/5eb73fd2-64cf-4ac3-8777-1aaba18c5e1e

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Quotient
import Mathlib.Data.Sym.Sym2
import Definitions.Def_BKAR_Forest
import Theorems.Thm_BKAR_Forest_pathInF_isSimple
import Theorems.Thm_BKAR_Forest_isSimplePath_of_edges_eq

set_option autoImplicit false
open BKAR
open BKAR.Forest
variable {V} [Fintype V] [DecidableEq V]
namespace BKAR.Forest
theorem _root_.solution
    (F G : Forest V) (hedges : F.edges = G.edges)
    {i j : V} (h : F.inSameComponent i j) :
    G.inSameComponent i j :=
  G.inSameComponent_of_isSimplePath
    (F.isSimplePath_of_edges_eq G hedges (F.pathInF_isSimple h))
end BKAR.Forest
