-- Prove2me | solution 1 for FiniteGraph.exists_maximal_supergraph_with_property
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T13:17:10.621506+00:00
-- url     : https://prove2.me/submissions/50493bb2-19a7-4a2c-924c-9d5905669f20

import Mathlib
theorem solution
    {V : Type} [Fintype V]
    (P : SimpleGraph V → Prop)
    (G : SimpleGraph V)
    (hG : P G) :
    ∃ F : SimpleGraph V,
      G.edgeSet ⊆ F.edgeSet ∧ P F ∧
        ∀ H : SimpleGraph V, F.edgeSet ⊆ H.edgeSet → P H → H.edgeSet = F.edgeSet := by
  classical
  obtain ⟨Qx9, hQm, hmax⟩ := (Finset.univ.filter (fun X0 : SimpleGraph V => G ≤ X0 ∧ P X0)).exists_max_image
    (fun X0 => X0.edgeFinset.card) ⟨G, Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_rfl, hG⟩⟩
  obtain ⟨hPQ, hQ⟩ : G ≤ Qx9 ∧ P Qx9 := (Finset.mem_filter.mp hQm).2
  have key : ∀ Rx9 : SimpleGraph V, Qx9 ≤ Rx9 → P Rx9 → Rx9 = Qx9 := by
    intro Rx9 hQR hR
    by_contra hne
    have hlt : Qx9 < Rx9 := lt_of_le_of_ne hQR (Ne.symm hne)
    have h2 := Finset.card_lt_card (SimpleGraph.edgeFinset_ssubset_edgeFinset.mpr hlt)
    have h3 := hmax Rx9 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hPQ.trans hQR, hR⟩)
    omega
  refine ⟨Qx9, ?_⟩
  repeat' apply And.intro
  all_goals first
    | exact hQ
    | exact hPQ
    | exact SimpleGraph.edgeSet_subset_edgeSet.mpr hPQ
    | exact fun _ _ h => hPQ h
    | (apply SimpleGraph.Connected.mono hPQ; assumption)
    | exact Set.ncard_le_ncard (SimpleGraph.edgeSet_subset_edgeSet.mpr hPQ) (Set.toFinite _)
    | (intro Rx9 ha hb; have e := key Rx9 (by first | exact ha | exact SimpleGraph.edgeSet_subset_edgeSet.mp ha | exact fun _ _ h => ha h | exact ha.le | exact SimpleGraph.edgeSet_subset_edgeSet.mp ha.subset) hb; subst e; first | rfl | exact le_rfl | exact subset_rfl | exact fun _ _ h => h)
    | (intro Rx9 hb ha; have e := key Rx9 (by first | exact ha | exact SimpleGraph.edgeSet_subset_edgeSet.mp ha | exact fun _ _ h => ha h | exact ha.le | exact SimpleGraph.edgeSet_subset_edgeSet.mp ha.subset) hb; subst e; first | rfl | exact le_rfl | exact subset_rfl | exact fun _ _ h => h)
    | (intro Rx9 ha hb hc; have e := key Rx9 (by first | exact ha | exact SimpleGraph.edgeSet_subset_edgeSet.mp ha | exact fun _ _ h => ha h | exact ha.le | exact SimpleGraph.edgeSet_subset_edgeSet.mp ha.subset) hc; subst e; exact absurd rfl hb)
    | (intro Rx9 ha hb; have e := key Rx9 (SimpleGraph.edgeSet_subset_edgeSet.mp ha.subset) hb; subst e; exact (ha.ne rfl).elim)
    | (intro Rx9 ha hb; have e := key Rx9 (SimpleGraph.edgeSet_subset_edgeSet.mp ha.subset) hb; subst e; exact (ha.ne rfl))
    | (intro Rx9 ha hb; have hm := hmax Rx9 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha, hb⟩); simp only [← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset]; exact hm)
