-- Prove2me | solution 1 for BiAbduction.Footprint.lemma_3_12
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-28T05:04:02.639418+00:00
-- url     : https://prove2.me/submissions/5b236f46-e8d4-4477-a946-9fc3344700a7

import Mathlib
import Definitions.Def_BiAbduction_Footprint_Semantics

open BiAbduction.Footprint

namespace SolBiAbductionFootprintLemma312

private def emptyHeap : Heap where
  cell := fun _ => none
  nil_unalloc := rfl
  finite_dom := by simp

private theorem union_swap {h a b : Heap} (hu : Heap.IsUnion h a b) :
    Heap.IsUnion h b a := by
  refine ⟨fun l => (hu.1 l).symm, ?_⟩
  intro l
  rcases hu.1 l with ha | hb
  · simp [hu.2 l, ha]
  · simp [hu.2 l, hb]

private theorem isUnion_empty_right (h : Heap) :
    Heap.IsUnion h h emptyHeap := by
  refine ⟨fun _ => Or.inr rfl, ?_⟩
  intro l
  cases h.cell l <;> rfl

private theorem subset_sepConj_univ (A : Pred) :
    A ⊆ sepConj A Set.univ := by
  rintro ⟨s, h⟩ hp
  exact ⟨h, emptyHeap, isUnion_empty_right h, hp, trivial⟩

private theorem isSolution_iff_entails_wand (F G M : Pred) :
    IsSolution F G M ↔ Entails M (wand F G) := by
  constructor
  · intro hSol p hpM h₀ hu h_union hF
    exact hSol ⟨h₀, p.2, union_swap h_union, hF, hpM⟩
  · rintro hEnt ⟨s, hu⟩ ⟨h₀, h₁, h_union, hF, hM⟩
    exact hEnt hM h₀ hu (union_swap h_union) hF

end SolBiAbductionFootprintLemma312

open SolBiAbductionFootprintLemma312

theorem solution (F G : Pred) :
    IsSolution F G (wand F G) ∧
    (∀ M : Pred, IsSolution F G M → SpatialLe (wand F G) M) ∧
    (∀ M : Pred, IsSolution F G M ↔ Entails M (wand F G)) := by
  refine ⟨?_, ?_, isSolution_iff_entails_wand F G⟩
  · exact (isSolution_iff_entails_wand F G (wand F G)).mpr Set.Subset.rfl
  · intro M hSol
    have hEnt : M ⊆ wand F G := (isSolution_iff_entails_wand F G M).mp hSol
    exact hEnt.trans (subset_sepConj_univ (wand F G))
