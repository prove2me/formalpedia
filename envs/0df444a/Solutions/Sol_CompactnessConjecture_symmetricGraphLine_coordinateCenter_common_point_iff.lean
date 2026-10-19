-- Prove2me | solution 1 for CompactnessConjecture.symmetricGraphLine_coordinateCenter_common_point_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:00.811989+00:00
-- url     : https://prove2.me/submissions/b5b7d6ac-f10f-4f2f-98c8-7a32ee16ea84

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_CompactnessConjecture_symmetricGraphLine_coordinateCenter_intersection_iff

set_option autoImplicit true
open CompactnessConjecture
noncomputable section
variable (K : Type*) [Field K]
namespace CompactnessConjecture
theorem _root_.solution
    {a b c x y : K} (hxy : x ≠ 0 ∨ y ≠ 0) :
    (∃ p : SymplecticPoint K,
      p.1 ≤ (symmetricGraphLine K a b c).1 ∧
        p.1 ≤ (coordinateCenterLine K x y hxy).1) ↔
      symmetricQuadratic a b c x y = 0 := by
  rw [← symmetricGraphLine_coordinateCenter_intersection_iff K hxy]
  constructor
  · rintro ⟨p, hpgraph, hpcenter⟩
    have hpbot : p.1 ≠ ⊥ := by
      intro hbot
      have hrank := p.2
      rw [hbot, finrank_bot] at hrank
      omega
    obtain ⟨w, hw, hwne⟩ :=
      Submodule.exists_mem_ne_zero_of_ne_bot hpbot
    exact ⟨w, hwne, hpgraph hw, hpcenter hw⟩
  · rintro ⟨w, hwne, hwgraph, hwcenter⟩
    let p : SymplecticPoint K :=
      ⟨K ∙ w, finrank_span_singleton hwne⟩
    refine ⟨p, ?_, ?_⟩
    · exact (Submodule.span_le).mpr (by simpa using hwgraph)
    · exact (Submodule.span_le).mpr (by simpa using hwcenter)
end CompactnessConjecture
