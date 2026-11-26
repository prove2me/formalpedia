-- Prove2me | solution 1 for BKAR.Forest.pathInF_eq_of_edges_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:04:04.52982+00:00
-- url     : https://prove2.me/submissions/c34e35bd-7d0a-4a43-a1ee-f4312889b287

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Quotient
import Mathlib.Data.Sym.Sym2
import Definitions.Def_BKAR_Forest
import Theorems.Thm_BKAR_Forest_pathInF_isSimple
import Theorems.Thm_BKAR_Forest_pathInF_unique
import Theorems.Thm_BKAR_Forest_isSimplePath_of_edges_eq

set_option autoImplicit false
open BKAR
open BKAR.Forest
variable {V} [Fintype V] [DecidableEq V]
namespace BKAR.Forest
theorem _root_.solution
    (F G : Forest V) (hedges : F.edges = G.edges)
    {i j : V} (hF : F.inSameComponent i j)
    (hG : G.inSameComponent i j) :
    F.pathInF i j hF = G.pathInF i j hG := by
  symm
  exact F.pathInF_unique hF (G.pathInF i j hG)
    (G.isSimplePath_of_edges_eq F hedges.symm (G.pathInF_isSimple hG))
end BKAR.Forest
