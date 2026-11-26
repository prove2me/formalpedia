-- Prove2me | solution 1 for BKAR.Forest.pathInF_eq_singleton_of_edge_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:03:57.777517+00:00
-- url     : https://prove2.me/submissions/9c03355b-34dd-4db1-a61c-b87e19be644b

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Quotient
import Mathlib.Data.Sym.Sym2
import Definitions.Def_BKAR_Forest
import Theorems.Thm_BKAR_Forest_pathInF_unique

set_option autoImplicit false
open BKAR
open BKAR.Forest
variable {V} [Fintype V] [DecidableEq V]
namespace BKAR.Forest
theorem _root_.solution (F : Forest V) {e : Edge V}
    (he : e ∈ F.edges) :
    F.pathInF e.left e.right (F.edge_inSameComponent he) = [e] :=
  (F.pathInF_unique (F.edge_inSameComponent he) [e] (F.edge_isSimplePath he)).symm
end BKAR.Forest
