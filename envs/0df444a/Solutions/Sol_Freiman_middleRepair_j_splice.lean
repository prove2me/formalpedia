-- Prove2me | solution 1 for Freiman.middleRepair_j_splice
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T22:56:29.897935+00:00
-- url     : https://prove2.me/submissions/b596a89b-5faf-46a2-8d8f-5b671c068959

import Definitions.Def_Freiman_middleRepair
import Mathlib.Data.List.GetD
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.Linarith

open Freiman

private theorem union_eq (cs : List MiddleCore) :
    middleUnion cs = ⋃ i ∈ Set.Iio cs.length, middleCover (cs.getD i ⟨[],[]⟩) := by
  ext t
  constructor
  · rintro ⟨d, hd, ht⟩
    obtain ⟨i, hi, hdi⟩ := List.mem_iff_getElem.mp hd
    apply Set.mem_iUnion.mpr ⟨i, ?_⟩
    apply Set.mem_iUnion.mpr ⟨hi, ?_⟩
    simpa only [List.getD_eq_getElem _ _ hi, hdi] using ht
  · intro ht
    obtain ⟨i, ht⟩ := Set.mem_iUnion.mp ht
    obtain ⟨hi, ht⟩ := Set.mem_iUnion.mp ht
    refine ⟨cs.getD i ⟨[],[]⟩, ?_, ht⟩
    rw [List.getD_eq_getElem _ _ hi]
    exact List.getElem_mem hi

theorem solution :
    ∀ (c : MiddleCore) (cs : List MiddleCore), middleContacts cs → middleRepairJAnchors c cs →
      (middleCover (middleRepairJ c 1)).Nonempty → middleCover c ⊆ middleUnion cs ∪ middleRepairJSpan c := by
  intro c cs hcs ha hj
  have hcs' : IsPreconnected (middleUnion cs) := by
    rw [union_eq]
    apply IsPreconnected.biUnion_of_chain Set.ordConnected_Iio
    · intro n hn
      exact isPreconnected_Icc
    · intro n hn hn'
      exact hcs.2 n hn'
  have hJ1 : middleCover (middleRepairJ c 1) ⊆ middleRepairJSpan c := by
    intro x hx
    exact ⟨(min_le_left _ _).trans hx.1, hx.2.trans (le_max_left _ _)⟩
  have hJ2 : middleCover (middleRepairJ c 2) ⊆ middleRepairJSpan c := by
    intro x hx
    exact ⟨(min_le_right _ _).trans hx.1, hx.2.trans (le_max_right _ _)⟩
  obtain ⟨d, hd, x, hxJ, hxd⟩ := ha.1
  have hinter : (middleUnion cs ∩ middleRepairJSpan c).Nonempty :=
    ⟨x,⟨d,hd,hxd⟩,hJ2 hxJ⟩
  have hall : IsPreconnected (middleUnion cs ∪ middleRepairJSpan c) :=
    IsPreconnected.union' hinter hcs' isPreconnected_Icc
  obtain ⟨z,hz⟩ := hj
  have hJlo : (middleBounds (middleRepairJ c 1)).1 ∈ middleUnion cs ∪ middleRepairJSpan c :=
    Or.inr (hJ1 ⟨le_rfl,hz.1.trans hz.2⟩)
  have hJhi : (middleBounds (middleRepairJ c 1)).2 ∈ middleUnion cs ∪ middleRepairJSpan c :=
    Or.inr (hJ1 ⟨hz.1.trans hz.2,le_rfl⟩)
  intro t ht
  rcases ha.2 with ⟨hlo,e,he,hhi⟩ | ⟨hhi,e,he,hlo⟩
  · obtain ⟨v,hv⟩ := hcs.1 e he
    have hehi : (middleBounds e).2 ∈ middleUnion cs ∪ middleRepairJSpan c :=
      Or.inl ⟨e,he,hv.1.trans hv.2,le_rfl⟩
    exact hall.ordConnected.out hJlo hehi ⟨hlo.trans ht.1,ht.2.trans hhi⟩
  · obtain ⟨v,hv⟩ := hcs.1 e he
    have helo : (middleBounds e).1 ∈ middleUnion cs ∪ middleRepairJSpan c :=
      Or.inl ⟨e,he,le_rfl,hv.1.trans hv.2⟩
    exact hall.ordConnected.out helo hJhi ⟨hlo.trans ht.1,ht.2.trans hhi⟩

#print axioms solution
