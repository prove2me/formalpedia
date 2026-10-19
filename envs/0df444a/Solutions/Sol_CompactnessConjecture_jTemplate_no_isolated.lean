-- Prove2me | solution 1 for CompactnessConjecture.jTemplate_no_isolated
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:35:58.946881+00:00
-- url     : https://prove2.me/submissions/a25a202b-a8a5-4d6e-86bf-82db6b958e81

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy

set_option autoImplicit true
open CompactnessConjecture
noncomputable section
open SimpleGraph
namespace CompactnessConjecture
theorem _root_.solution :
    GraphHasNoIsolated jTemplate := by
  intro u
  rcases u with (base | ⟨copy, center⟩) |
    (⟨copy, ⟨base, center⟩⟩ | lastVertex)
  · fin_cases base
    · refine ⟨.inr (.inr ()), ?_⟩
      simp [jTemplate, SimpleGraph.fromRel_adj, jTemplateRelation]
    · refine ⟨.inr (.inr ()), ?_⟩
      simp [jTemplate, SimpleGraph.fromRel_adj, jTemplateRelation]
    · refine ⟨.inr (.inl (0, (1, 0))), ?_⟩
      simp [jTemplate, SimpleGraph.fromRel_adj,
        jTemplateRelation, jBase]
    · refine ⟨.inr (.inl (0, (2, 0))), ?_⟩
      simp [jTemplate, SimpleGraph.fromRel_adj,
        jTemplateRelation, jBase]
  · refine ⟨.inr (.inl (copy, (0, center))), ?_⟩
    simp [jTemplate, SimpleGraph.fromRel_adj, jTemplateRelation]
  · refine ⟨.inl (.inl (jBase copy base)), ?_⟩
    simp [jTemplate, SimpleGraph.fromRel_adj, jTemplateRelation]
  · refine ⟨.inl (.inl 0), ?_⟩
    cases lastVertex
    simp [jTemplate, SimpleGraph.fromRel_adj, jTemplateRelation]
end CompactnessConjecture
