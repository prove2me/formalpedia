-- Prove2me | solution 1 for ChromaticReconstruction.chromSymm_iso
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T15:24:18.031333+00:00
-- url     : https://prove2.me/submissions/0cc0c379-9bd1-4660-a1a2-261458c134ad

import Definitions.Def_RequestProject_Defs
import Definitions.Def_RequestProject_Components
import Theorems.Thm_ChromaticReconstruction_typeMonomial_map_equiv
import Theorems.Thm_ChromaticReconstruction_edgeFinset_map_iso

set_option autoImplicit true
open MvPolynomial Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
variable {V W : Type*}
variable [Fintype V] [Fintype W]
namespace ChromaticReconstruction
theorem _root_.solution {G : SimpleGraph V} {G' : SimpleGraph W} (e : G ≃g G') :
    chromSymm G = chromSymm G' := by
  unfold chromSymm
  rw [edgeFinset_map_iso e]
  have h1 : ∀ x, e.toEquiv.symm (e x) = x := fun x => e.toEquiv.symm_apply_apply x
  have h2 : ∀ x, e (e.toEquiv.symm x) = x := fun x => e.toEquiv.apply_symm_apply x
  refine Finset.sum_nbij' (fun A => A.map e.toEquiv.toEmbedding.sym2Map)
    (fun B => B.map e.toEquiv.symm.toEmbedding.sym2Map) ?_ ?_ ?_ ?_ ?_
  · intro A hA
    simp only [mem_powerset] at hA ⊢
    exact Finset.map_subset_map.2 hA
  · intro B hB
    simp only [mem_powerset] at hB ⊢
    intro z hz
    obtain ⟨y, hy, rfl⟩ := mem_map.1 hz
    obtain ⟨x, hx, rfl⟩ := mem_map.1 (hB hy)
    simpa [Sym2.map_map, h1] using hx
  · intro A _
    ext z; simp [Sym2.map_map, h1]
  · intro B _
    ext z; simp [Sym2.map_map, h2]
  · intro A _
    simp only [card_map, coe_map]
    congr 1
    exact (typeMonomial_map_equiv e.toEquiv A).symm
end ChromaticReconstruction
