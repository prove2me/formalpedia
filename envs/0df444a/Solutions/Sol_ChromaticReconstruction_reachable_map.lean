-- Prove2me | solution 1 for ChromaticReconstruction.reachable_map
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T11:07:51.223824+00:00
-- url     : https://prove2.me/submissions/66de6cf3-e295-41ca-bfec-99b6e1acff2c

import Definitions.Def_RequestProject_Defs
import Definitions.Def_RequestProject_Components

set_option autoImplicit true
open MvPolynomial Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
variable {V W : Type*}
namespace ChromaticReconstruction
theorem _root_.solution (f : V → W) (A : Set (Sym2 V)) (B : Set (Sym2 W))
    (h : ∀ u v, s(u, v) ∈ A → u ≠ v → f u = f v ∨ s(f u, f v) ∈ B) {u v : V}
    (huv : (SimpleGraph.fromEdgeSet A).Reachable u v) :
    (SimpleGraph.fromEdgeSet B).Reachable (f u) (f v) := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at huv ⊢
  induction huv with
  | refl => exact Relation.ReflTransGen.refl
  | @tail b c _ hbc ih =>
    rw [SimpleGraph.fromEdgeSet_adj] at hbc
    rcases h _ _ hbc.1 hbc.2 with he | he
    · rwa [← he]
    · by_cases hne : f b = f c
      · rwa [← hne]
      · exact ih.tail (by rw [SimpleGraph.fromEdgeSet_adj]; exact ⟨he, hne⟩)
end ChromaticReconstruction
