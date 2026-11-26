-- Prove2me | solution 1 for BKAR.Forest.edge_mem_of_isSimplePath
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:03:46.198627+00:00
-- url     : https://prove2.me/submissions/e42241a2-7d25-48de-8386-f2d42e0b267e

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
    {γ : List (Edge V)} (hγ : IsSimplePath F γ i j) :
    ∀ e ∈ γ, e ∈ F.edges :=
  F.acyclic.path_edges_mem hγ
end BKAR.Forest
