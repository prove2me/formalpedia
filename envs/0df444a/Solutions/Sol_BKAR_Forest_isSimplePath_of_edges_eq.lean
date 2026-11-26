-- Prove2me | solution 1 for BKAR.Forest.isSimplePath_of_edges_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:02:27.04213+00:00
-- url     : https://prove2.me/submissions/33ea687d-befc-4692-ab34-5a40caeb1bd1

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
theorem _root_.solution
    (F G : Forest V) (hedges : F.edges = G.edges)
    {γ : List (Edge V)} {i j : V}
    (hγ : IsSimplePath F γ i j) :
    IsSimplePath G γ i j := by
  rw [IsSimplePath]
  rw [G.acyclic.isSimplePath_iff]
  rw [← hedges]
  exact F.acyclic.isSimplePath_iff.mp hγ
end BKAR.Forest
