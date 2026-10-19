-- Prove2me | solution 1 for CompactnessConjecture.jTemplate_connected
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:04.05007+00:00
-- url     : https://prove2.me/submissions/76527a59-3b04-4774-aa54-745d70f67ac3

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy

set_option autoImplicit true
open CompactnessConjecture
noncomputable section
open Finset SimpleGraph
namespace CompactnessConjecture
theorem _root_.solution : jTemplate.Connected := by
  apply (SimpleGraph.connected_iff_exists_forall_reachable jTemplate).2
  let root : JVertex := .inl (.inl (2 : Fin 4))
  refine ⟨root, ?_⟩
  have hbasePair (copy : Fin 2) (base : Fin 3) (center : Fin 2) :
      jTemplate.Adj
        (.inl (.inl (jBase copy base)))
        (.inr (.inl (copy, (base, center)))) := by
    simp [jTemplate, SimpleGraph.fromRel_adj, jTemplateRelation]
  have hcenterPair (copy : Fin 2) (base : Fin 3) (center : Fin 2) :
      jTemplate.Adj
        (.inl (.inr (copy, center)))
        (.inr (.inl (copy, (base, center)))) := by
    simp [jTemplate, SimpleGraph.fromRel_adj, jTemplateRelation]
  have hrootCenter (copy : Fin 2) (center : Fin 2) :
      jTemplate.Reachable root (.inl (.inr (copy, center))) := by
    have hfirst :
        jTemplate.Adj root
          (.inr (.inl (copy, ((1 : Fin 3), center)))) := by
      simpa [root, jBase] using hbasePair copy 1 center
    exact hfirst.reachable.trans
      (hcenterPair copy 1 center).symm.reachable
  have hrootPair (copy : Fin 2) (base : Fin 3) (center : Fin 2) :
      jTemplate.Reachable root
        (.inr (.inl (copy, (base, center)))) :=
    (hrootCenter copy center).trans (hcenterPair copy base center).reachable
  have hrootBase (copy : Fin 2) (base : Fin 3) :
      jTemplate.Reachable root (.inl (.inl (jBase copy base))) :=
    (hrootPair copy base 0).trans (hbasePair copy base 0).symm.reachable
  intro vertex
  rcases vertex with (base | ⟨copy, center⟩) |
      (⟨copy, ⟨base, center⟩⟩ | lastVertex)
  · fin_cases base
    · simpa [jBase] using hrootBase 0 0
    · simpa [jBase] using hrootBase 1 0
    · simpa [jBase] using hrootBase 0 1
    · simpa [jBase] using hrootBase 0 2
  · exact hrootCenter copy center
  · exact hrootPair copy base center
  · cases lastVertex
    have hjoin :
        jTemplate.Adj (.inl (.inl (0 : Fin 4)))
          (.inr (.inr ())) := by
      simp [jTemplate, SimpleGraph.fromRel_adj, jTemplateRelation]
    have hzero :
        jTemplate.Reachable root (.inl (.inl (0 : Fin 4))) := by
      simpa [jBase] using hrootBase 0 0
    exact hzero.trans hjoin.reachable
end CompactnessConjecture
