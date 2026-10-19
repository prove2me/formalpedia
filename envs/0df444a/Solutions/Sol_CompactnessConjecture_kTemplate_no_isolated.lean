-- Prove2me | solution 1 for CompactnessConjecture.kTemplate_no_isolated
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:35:58.946881+00:00
-- url     : https://prove2.me/submissions/6315d58c-ce05-485b-a05a-511676dc4e24

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy

set_option autoImplicit true
open CompactnessConjecture
noncomputable section
open SimpleGraph
namespace CompactnessConjecture
theorem _root_.solution :
    GraphHasNoIsolated kTemplate := by
  intro u
  rcases u with ⟨copy, (base | center) | ⟨base, center⟩⟩
  · refine ⟨(copy, .inr (base, 0)), ?_⟩
    simp [kTemplate, SimpleGraph.fromRel_adj,
      kTemplateRelation, subdivisionRelation]
  · refine ⟨(copy, .inr (0, center)), ?_⟩
    simp [kTemplate, SimpleGraph.fromRel_adj,
      kTemplateRelation, subdivisionRelation]
  · refine ⟨(copy, .inl (.inl base)), ?_⟩
    simp [kTemplate, SimpleGraph.fromRel_adj,
      kTemplateRelation, subdivisionRelation]
end CompactnessConjecture
