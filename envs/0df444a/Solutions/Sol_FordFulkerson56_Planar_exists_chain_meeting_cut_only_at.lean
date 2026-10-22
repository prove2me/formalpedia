-- Prove2me | solution 1 for FordFulkerson56.Planar.exists_chain_meeting_cut_only_at
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-22T01:51:39.083004+00:00
-- url     : https://prove2.me/submissions/4b976d97-191a-4fb3-a53a-acef8764ea46

import Mathlib
import Definitions.Def_FordFulkerson56_MinCut_Network
import Definitions.Def_FordFulkerson56_MinCut_IsChain
import Definitions.Def_FordFulkerson56_MinCut_IsDisconnecting



namespace FordFulkerson56.Planar

theorem chain_cut_core {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E]
    [DecidableEq E] (N : FordFulkerson56.MinCut.Network V E) (D : Finset E)
    (hD : FordFulkerson56.MinCut.IsCut N D) (α : E) (hα : α ∈ D) :
    ∃ C : Finset E, FordFulkerson56.MinCut.IsChain N N.source N.sink C ∧ C ∩ D = {α} := by
  obtain ⟨hdis, hmin⟩ := hD
  have h1 := hmin (D.erase α) (Finset.erase_ssubset hα)
  unfold FordFulkerson56.MinCut.IsDisconnecting at h1
  push Not at h1
  obtain ⟨C, hC, hC2'⟩ := h1
  have hC2 : ¬ (C ∩ D.erase α).Nonempty := by
    rw [Finset.not_nonempty_iff_eq_empty]; exact hC2'
  refine ⟨C, hC, ?_⟩
  obtain ⟨x, hx⟩ := hdis C hC
  have hxD : x ∈ D := (Finset.mem_inter.1 hx).2
  have hxC : x ∈ C := (Finset.mem_inter.1 hx).1
  have hxα : x = α := by
    by_contra hne
    exact hC2 ⟨x, Finset.mem_inter.2 ⟨hxC, Finset.mem_erase.2 ⟨hne, hxD⟩⟩⟩
  subst hxα
  ext y
  simp only [Finset.mem_inter, Finset.mem_singleton]
  constructor
  · rintro ⟨hyC, hyD⟩
    by_contra hne
    exact hC2 ⟨y, Finset.mem_inter.2 ⟨hyC, Finset.mem_erase.2 ⟨hne, hyD⟩⟩⟩
  · rintro rfl
    exact ⟨hxC, hxD⟩

end FordFulkerson56.Planar

open FordFulkerson56.Planar


theorem solution {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E]
    [DecidableEq E] (N : FordFulkerson56.MinCut.Network V E) (D : Finset E) (hD : FordFulkerson56.MinCut.IsCut N D) (α : E) (hα : α ∈ D) :
    ∃ C : Finset E, FordFulkerson56.MinCut.IsChain N N.source N.sink C ∧ C ∩ D = {α} := by
  exact chain_cut_core N D hD α hα
