-- Prove2me | solution 2 for ChromaticReconstruction.reachable_of_edges_reachable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T00:30:24.536841+00:00
-- url     : https://prove2.me/submissions/84c6ab0a-10e2-46eb-bf3e-53a21d88367c

import Definitions.Def_RequestProject_PathLeaf
import Definitions.Def_RequestProject_Truncation
import Definitions.Def_RequestProject_PathLeafSwap

set_option autoImplicit true
open Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
variable {n c : ℕ}
variable {V : Type*} [Fintype V]
omit [Fintype V]
namespace ChromaticReconstruction
theorem _root_.solution {A B : Set (Sym2 V)}
    (h : ∀ u v, s(u, v) ∈ A → (SimpleGraph.fromEdgeSet B).Reachable u v) {x y : V}
    (hxy : (SimpleGraph.fromEdgeSet A).Reachable x y) :
    (SimpleGraph.fromEdgeSet B).Reachable x y := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at hxy
  induction hxy with
  | refl => rfl
  | tail _ hbc ih =>
    rw [SimpleGraph.fromEdgeSet_adj] at hbc
    exact ih.trans (h _ _ hbc.1)
end ChromaticReconstruction
