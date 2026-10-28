-- Prove2me | solution 1 for FiniteGraph.connected_supergraph_of_step
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T13:16:48.715707+00:00
-- url     : https://prove2.me/submissions/c39c9f30-9400-4314-833d-74bf6133d0a6

import Mathlib

set_option autoImplicit false
theorem solution
    {V : Type} [Fintype V]
    (P : SimpleGraph V → Prop)
    (G : SimpleGraph V)
    (hG : P G)
    (hstep : ∀ F : SimpleGraph V, G.edgeSet ⊆ F.edgeSet → P F → ¬ F.Connected →
      ∃ H : SimpleGraph V,
        F.edgeSet ⊆ H.edgeSet ∧ P H ∧
          ∃ u v : V, ¬ F.Reachable u v ∧ H.Reachable u v) :
    ∃ H : SimpleGraph V,
      G.edgeSet ⊆ H.edgeSet ∧ P H ∧ H.Connected := by
  classical
  obtain ⟨Q, hQm, hmax⟩ := (Finset.univ.filter (fun X0 : SimpleGraph V => G ≤ X0 ∧ P X0)).exists_max_image
    (fun X0 => X0.edgeFinset.card) ⟨G, Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_rfl, hG⟩⟩
  obtain ⟨hGQ, hQ⟩ : G ≤ Q ∧ P Q := (Finset.mem_filter.mp hQm).2
  refine ⟨Q, SimpleGraph.edgeSet_subset_edgeSet.mpr hGQ, hQ, ?_⟩
  by_contra hc
  obtain ⟨L, hQL, hPL, u, v, hnQ, hL⟩ := hstep Q (SimpleGraph.edgeSet_subset_edgeSet.mpr hGQ) hQ hc
  have hQL' : Q ≤ L := SimpleGraph.edgeSet_subset_edgeSet.mp hQL
  have hne : Q ≠ L := fun h => hnQ (h ▸ hL)
  have hlt : Q < L := lt_of_le_of_ne hQL' hne
  have h2 := Finset.card_lt_card (SimpleGraph.edgeFinset_ssubset_edgeFinset.mpr hlt)
  have h3 := hmax L (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hGQ.trans hQL', hPL⟩)
  omega
