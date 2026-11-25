-- Prove2me | solution 1 for ChromaticReconstruction.compType_empty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T00:58:10.855308+00:00
-- url     : https://prove2.me/submissions/5747c79d-7ffc-46a4-9a1e-a69f8dc82c23

import Definitions.Def_RequestProject_PhiFormula
import Definitions.Def_RequestProject_CompStructure
import Theorems.Thm_ChromaticReconstruction_eq_compOf
import Theorems.Thm_ChromaticReconstruction_sum_card_compSets
import Theorems.Thm_ChromaticReconstruction_card_compType
import Theorems.Thm_ChromaticReconstruction_mem_compType
import Theorems.Thm_ChromaticReconstruction_killP1_X_one
import Theorems.Thm_ChromaticReconstruction_mem_of_reachable_of_closed
import Theorems.Thm_ChromaticReconstruction_nonempty_of_mem_compSets
attribute [local simp] ChromaticReconstruction.killP1_X_one



set_option autoImplicit true
open MvPolynomial Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
variable {V : Type*} [Fintype V]
namespace ChromaticReconstruction
theorem _root_.solution : compType (∅ : Set (Sym2 V)) = Multiset.replicate (Fintype.card V) 1 := by
  have hsing : ∀ C ∈ compSets (∅ : Set (Sym2 V)), C.card = 1 := by
    intro C hC
    obtain ⟨v, hv⟩ := nonempty_of_mem_compSets hC
    rw [eq_compOf hC hv, card_eq_one]
    refine ⟨v, ?_⟩
    ext w
    simp only [compOf, mem_filter, mem_univ, true_and, mem_singleton]
    constructor
    · intro h
      have := mem_of_reachable_of_closed (B := ({v} : Set V)) (by simp) rfl h
      simpa using this
    · rintro rfl; rfl
  rw [Multiset.eq_replicate]
  refine ⟨?_, fun r hr => ?_⟩
  · rw [card_compType, ← sum_card_compSets (∅ : Set (Sym2 V)), sum_congr rfl hsing]
    simp
  · obtain ⟨C, hC, rfl⟩ := mem_compType.1 hr
    exact hsing C hC
end ChromaticReconstruction
