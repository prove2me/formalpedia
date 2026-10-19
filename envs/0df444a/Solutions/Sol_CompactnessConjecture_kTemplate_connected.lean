-- Prove2me | solution 1 for CompactnessConjecture.kTemplate_connected
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:04.05007+00:00
-- url     : https://prove2.me/submissions/f1bb5b25-dd58-4ba1-a7fa-67e859076ce6

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy

set_option autoImplicit true
open CompactnessConjecture
noncomputable section
open Finset SimpleGraph
namespace CompactnessConjecture
theorem _root_.solution : kTemplate.Connected := by
  apply (SimpleGraph.connected_iff_exists_forall_reachable kTemplate).2
  let root : KVertex := ((0 : Fin 2), kSpecifiedCenter)
  refine ⟨root, ?_⟩
  have hbasePair (copy : Fin 2) (base : Fin 3) (center : Fin 3) :
      kTemplate.Adj
        (copy, .inl (.inl base))
        (copy, .inr (base, center)) := by
    simp [kTemplate, SimpleGraph.fromRel_adj, kTemplateRelation,
      subdivisionRelation]
  have hcenterPair (copy : Fin 2) (base : Fin 3) (center : Fin 3) :
      kTemplate.Adj
        (copy, .inl (.inr center))
        (copy, .inr (base, center)) := by
    simp [kTemplate, SimpleGraph.fromRel_adj, kTemplateRelation,
      subdivisionRelation]
  have hbridge :
      kTemplate.Adj root ((1 : Fin 2), kSpecifiedCenter) := by
    simp [root, kTemplate, SimpleGraph.fromRel_adj, kTemplateRelation,
      kSpecifiedCenter, subdivisionRelation]
  have hhub (copy : Fin 2) :
      kTemplate.Reachable root (copy, kSpecifiedCenter) := by
    fin_cases copy
    · exact SimpleGraph.Reachable.refl root
    · exact hbridge.reachable
  have hrootBase (copy : Fin 2) (base : Fin 3) :
      kTemplate.Reachable root (copy, .inl (.inl base)) := by
    have hfirst :
        kTemplate.Reachable root (copy, .inr (base, (0 : Fin 3))) := by
      exact (hhub copy).trans
        (by
          simpa [kSpecifiedCenter] using
            (hcenterPair copy base 0).reachable)
    exact hfirst.trans (hbasePair copy base 0).symm.reachable
  have hrootPair (copy : Fin 2) (base : Fin 3) (center : Fin 3) :
      kTemplate.Reachable root (copy, .inr (base, center)) :=
    (hrootBase copy base).trans (hbasePair copy base center).reachable
  have hrootCenter (copy : Fin 2) (center : Fin 3) :
      kTemplate.Reachable root (copy, .inl (.inr center)) :=
    (hrootPair copy 0 center).trans
      (hcenterPair copy 0 center).symm.reachable
  intro vertex
  rcases vertex with ⟨copy, (base | center) | ⟨base, center⟩⟩
  · exact hrootBase copy base
  · exact hrootCenter copy center
  · exact hrootPair copy base center
end CompactnessConjecture
