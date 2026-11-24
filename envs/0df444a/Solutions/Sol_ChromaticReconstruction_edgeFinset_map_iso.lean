-- Prove2me | solution 1 for ChromaticReconstruction.edgeFinset_map_iso
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T11:47:53.063803+00:00
-- url     : https://prove2.me/submissions/7e1cec21-eb42-44c8-9a59-44083d56c2b2

import Definitions.Def_RequestProject_Defs
import Definitions.Def_RequestProject_Components

set_option autoImplicit true
open MvPolynomial Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
variable {V W : Type*}
variable [Fintype V] [Fintype W]
namespace ChromaticReconstruction
theorem _root_.solution {G : SimpleGraph V} {G' : SimpleGraph W} (e : G ≃g G') :
    G'.edgeFinset = G.edgeFinset.map e.toEquiv.toEmbedding.sym2Map := by
  ext z
  induction z using Sym2.ind with
  | _ a b =>
    simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, mem_map]
    constructor
    · intro h
      refine ⟨s(e.symm a, e.symm b), ?_, ?_⟩
      · simpa using (e.symm.map_adj_iff).2 h
      · simp
    · rintro ⟨z, hz, hze⟩
      induction z using Sym2.ind with
      | _ c d =>
        simp only [SimpleGraph.mem_edgeSet] at hz
        simp only [Function.Embedding.sym2Map_apply, Sym2.map_pair_eq, Sym2.eq_iff] at hze
        rcases hze with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · simpa using (e.map_adj_iff).2 hz
        · simpa using (e.map_adj_iff).2 hz.symm
end ChromaticReconstruction
