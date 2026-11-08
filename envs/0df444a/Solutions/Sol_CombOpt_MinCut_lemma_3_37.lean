-- Prove2me | solution 1 for CombOpt.MinCut.lemma_3_37
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T15:15:05.010277+00:00
-- url     : https://prove2.me/submissions/e979630e-bad7-401c-add3-c2b80143dc17

import Mathlib
import Definitions.Def_CombOpt_MinCut_CapGraph
import Definitions.Def_CombOpt_MinCut_CapGraph_minCutValue

open CombOpt.MinCut in
theorem solution {V E : Type*} [Fintype V] [Fintype E] (G : CombOpt.MinCut.CapGraph V E) (p q r : V) :
    min (G.minCutValue r q) (G.minCutValue p r) ≤ G.minCutValue p q := by
  classical
  unfold CombOpt.MinCut.CapGraph.minCutValue
  apply Finset.le_inf
  intro S hS
  rw [Finset.mem_filter] at hS
  have hs := hS.2
  have key : CombOpt.MinCut.Separates S r q ∨ CombOpt.MinCut.Separates S p r := by
    unfold CombOpt.MinCut.Separates at *
    rw [xor_def] at hs
    rw [xor_def, xor_def]
    tauto
  rcases key with h | h
  · exact (min_le_left _ _).trans (Finset.inf_le (Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩))
  · exact (min_le_right _ _).trans (Finset.inf_le (Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩))
