-- Prove2me | solution 1 for ChromaticReconstruction.bigParts_facts
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:33:17.359049+00:00
-- url     : https://prove2.me/submissions/5aa146b7-60af-4db4-8784-37754e7c8d13

import Definitions.Def_RequestProject_Truncation
import Definitions.Def_RequestProject_Forest
import Definitions.Def_RequestProject_CountingUpper
import Theorems.Thm_ChromaticReconstruction_sum_parts_sub_one_add_card
import Theorems.Thm_ChromaticReconstruction_killP1_X_one
attribute [local simp] ChromaticReconstruction.killP1_X_one



set_option autoImplicit true
open Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
namespace ChromaticReconstruction
theorem _root_.solution {k t : ℕ} {μ : Nat.Partition k} (hμ : k - t ≤ Multiset.card μ.parts) :
    Multiset.card (bigParts μ) ≤ t ∧ ∀ a ∈ bigParts μ, a ≤ t + 1 := by
  have hs := sum_parts_sub_one_add_card μ
  have hsplit := Multiset.filter_add_not (2 ≤ ·) μ.parts
  have hbig : ((bigParts μ).map fun a => a - 1).sum ≤ t := by
    have : ((bigParts μ).map fun a => a - 1).sum ≤ (μ.parts.map fun a => a - 1).sum := by
      conv_rhs => rw [← hsplit]
      rw [Multiset.map_add, Multiset.sum_add]
      exact Nat.le_add_right _ _
    omega
  refine ⟨?_, fun a ha => ?_⟩
  · have : Multiset.card (bigParts μ) ≤ ((bigParts μ).map fun a => a - 1).sum := by
      have := Multiset.sum_map_le_sum_map (s := bigParts μ) (fun _ => 1) (fun a => a - 1)
        (fun a ha => by
          have : 2 ≤ a := (Multiset.mem_filter.1 ha).2
          show 1 ≤ a - 1
          omega)
      simpa using this
    omega
  · have h1 : a - 1 ≤ ((bigParts μ).map fun a => a - 1).sum :=
      Multiset.le_sum_of_mem (Multiset.mem_map_of_mem (fun a => a - 1) ha)
    omega
end ChromaticReconstruction
