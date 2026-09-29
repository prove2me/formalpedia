-- Prove2me | solution 1 for Freiman.middle_interval_chain
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T22:47:54.532973+00:00
-- url     : https://prove2.me/submissions/8da306fb-c4b2-45fa-b898-c70e7c743b09

import Definitions.Def_Freiman_middleRoots
import Mathlib.Data.List.GetD
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.Linarith
open Freiman
set_option autoImplicit false

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
    ∀ (cs : List MiddleCore) (l u : ℝ), middleContacts cs →
      (∃ d ∈ cs, (middleBounds d).1 ≤ l) → (∃ d ∈ cs, u ≤ (middleBounds d).2) →
      Set.Icc l u ⊆ middleUnion cs := by
  intro cs l u hc hl hu
  have hc' : IsPreconnected (middleUnion cs) := by
    rw [union_eq]
    apply IsPreconnected.biUnion_of_chain Set.ordConnected_Iio
    · intro n hn
      exact isPreconnected_Icc
    · intro n hn hn'
      exact hc.2 n hn'
  obtain ⟨d, hd, hdl⟩ := hl
  obtain ⟨e, he, heu⟩ := hu
  obtain ⟨v, hv⟩ := hc.1 d hd
  obtain ⟨w, hw⟩ := hc.1 e he
  have hdmem : (middleBounds d).1 ∈ middleUnion cs := by
    exact ⟨d, hd, le_rfl, hv.1.trans hv.2⟩
  have hemem : (middleBounds e).2 ∈ middleUnion cs := by
    exact ⟨e, he, hw.1.trans hw.2, le_rfl⟩
  intro t ht
  exact hc'.ordConnected.out hdmem hemem ⟨hdl.trans ht.1, ht.2.trans heu⟩
#print axioms solution
