-- Prove2me | solution 1 for DeletionCode.ComponentBounds.incident_union_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:15:50.157866+00:00
-- url     : https://prove2.me/submissions/68f7ae50-7c53-463e-8b29-6db3e20ec5a2

import Definitions.Def_DeletionCode_RuleSetGraph
import Mathlib.Data.Fintype.Sum
import Definitions.Def_DeletionCode_ComponentBounds

set_option autoImplicit true
open DeletionCode DeletionCode.ComponentBounds
open SignedSupport SupportComponents RuleSetGraph
namespace DeletionCode.ComponentBounds
theorem _root_.solution {L : ℕ} (Q S : Finset (Gram L → ℤ)) (v : Vertex L) :
    Incident (Q ∪ S) v ↔ Incident Q v ∨ Incident S v := by
  classical
  constructor
  · rintro ⟨u, ⟨w, hw, g, hg, hv, hu⟩ | ⟨w, hw, g, hg, hu, hv⟩⟩
    · rcases Finset.mem_union.mp hw with hw | hw
      · exact Or.inl ⟨u, Or.inl ⟨w, hw, g, hg, hv, hu⟩⟩
      · exact Or.inr ⟨u, Or.inl ⟨w, hw, g, hg, hv, hu⟩⟩
    · rcases Finset.mem_union.mp hw with hw | hw
      · exact Or.inl ⟨u, Or.inr ⟨w, hw, g, hg, hu, hv⟩⟩
      · exact Or.inr ⟨u, Or.inr ⟨w, hw, g, hg, hu, hv⟩⟩
  · rintro (h | h)
    · exact incident_mono Finset.subset_union_left h
    · exact incident_mono Finset.subset_union_right h
end DeletionCode.ComponentBounds
