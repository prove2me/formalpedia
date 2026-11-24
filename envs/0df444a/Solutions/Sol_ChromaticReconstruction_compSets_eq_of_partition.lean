-- Prove2me | solution 1 for ChromaticReconstruction.compSets_eq_of_partition
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T11:26:33.306879+00:00
-- url     : https://prove2.me/submissions/73eb3fdd-ba2d-4449-aefd-48598edf72fa

import Definitions.Def_RequestProject_Defs
import Definitions.Def_RequestProject_Components
import Theorems.Thm_ChromaticReconstruction_mem_of_reachable_of_closed

set_option autoImplicit true
open MvPolynomial Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
variable {V W : Type*}
variable [Fintype V] [Fintype W]
namespace ChromaticReconstruction
theorem _root_.solution (A : Set (Sym2 V)) (P : Finset (Finset V))
    (hcover : ∀ v, ∃ B ∈ P, v ∈ B)
    (hne : ∀ B ∈ P, B.Nonempty)
    (hconn : ∀ B ∈ P, ∀ u ∈ B, ∀ w ∈ B, (SimpleGraph.fromEdgeSet A).Reachable u w)
    (hclosed : ∀ B ∈ P, ∀ u ∈ B, ∀ w, s(u, w) ∈ A → w ∈ B) :
    compSets A = P := by
  have key : ∀ B ∈ P, ∀ v ∈ B,
      (univ.filter fun w => (SimpleGraph.fromEdgeSet A).Reachable v w) = B := by
    intro B hB v hv
    ext w
    simp only [mem_filter, mem_univ, true_and]
    constructor
    · intro h
      exact mem_of_reachable_of_closed (B := (B : Set V)) (fun u hu w hw => hclosed B hB u hu w hw)
        hv h
    · intro hw
      exact hconn B hB v hv w hw
  ext B
  simp only [compSets, mem_image, mem_univ, true_and]
  constructor
  · rintro ⟨v, rfl⟩
    obtain ⟨B', hB', hv⟩ := hcover v
    rw [key B' hB' v hv]
    exact hB'
  · intro hB
    obtain ⟨v, hv⟩ := hne B hB
    exact ⟨v, key B hB v hv⟩
end ChromaticReconstruction
