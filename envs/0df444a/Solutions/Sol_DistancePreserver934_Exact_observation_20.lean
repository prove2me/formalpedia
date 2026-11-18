-- Prove2me | solution 1 for DistancePreserver934.Exact.observation_20
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-17T23:58:01.293407+00:00
-- url     : https://prove2.me/submissions/b19e2c10-a1c0-4eeb-80f6-880be6a49954

import Definitions.Def_DistancePreserver934_Exact_Essential

set_option autoImplicit false
open Classical DistancePreserver934.Exact

private lemma essential_mem {V : Type} [Fintype V] (K K' : SimpleGraph V)
    (R : Finset (Sym2 V)) (hR : IsDemandSet K R) (hK' : IsPreserver K K' R)
    (q e : Sym2 V) (hq : q ∈ R) (he : IsEssential K q e) : e ∈ K'.edgeSet := by
  induction q using Sym2.ind with
  | _ s t =>
    have hr : K'.Reachable s t := SimpleGraph.edist_ne_top_iff_reachable.mp (by
      rw [hK'.2 s t hq]; exact SimpleGraph.edist_ne_top_iff_reachable.mpr (hR s t hq).2)
    obtain ⟨w, hw⟩ := hr.exists_walk_length_eq_edist
    have hw' : IsShortest (w.mapLe hK'.1) := by
      simpa [IsShortest, hK'.2 s t hq] using hw
    have hm := he s t rfl (w.mapLe hK'.1) hw'
    rw [SimpleGraph.Walk.edges_mapLe_eq_edges] at hm
    exact w.edges_subset_edgeSet hm

private lemma minimal_essential {V : Type} [Fintype V] (K : SimpleGraph V)
    (R : Finset (Sym2 V)) (hR : IsDemandSet K R) (hK : IsMinimalPreserver K K R)
    (e : Sym2 V) (he : e ∈ K.edgeSet) : (essSet K R e).Nonempty := by
  by_contra hn
  have hnone : ∀ q ∈ R, ¬ IsEssential K q e := by
    intro q hq hess
    exact hn ⟨q, Finset.mem_filter.mpr ⟨hq, hess⟩⟩
  apply hK.2 e he
  refine ⟨K.deleteEdges_le _, ?_⟩
  intro s t hst
  have hnot := hnone s(s,t) hst
  simp only [IsEssential, not_forall] at hnot
  obtain ⟨a,b,hab,w,hw,hew⟩ := hnot
  have hwlen : (w.length : ℕ∞) = K.edist s t := by
    rcases Sym2.eq_iff.mp hab with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact hw
    · simpa [IsShortest, SimpleGraph.edist_comm] using hw
  have hdist : (K.deleteEdges {e}).edist a b ≤ K.edist a b := by
    calc
      _ ≤ ((w.toDeleteEdge e hew).length : ℕ∞) := SimpleGraph.edist_le _
      _ = K.edist a b := by simpa [IsShortest, SimpleGraph.Walk.toDeleteEdge,
        SimpleGraph.Walk.toDeleteEdges, SimpleGraph.Walk.length_transfer] using hw
  have hdeq : (K.deleteEdges {e}).edist a b = K.edist a b :=
    le_antisymm hdist (SimpleGraph.edist_anti (K.deleteEdges_le _))
  rcases Sym2.eq_iff.mp hab with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · exact hdeq
  · simpa only [SimpleGraph.edist_comm] using hdeq

theorem solution {V : Type} [Fintype V] (K : SimpleGraph V) (R : Finset (Sym2 V))
    (hR : IsDemandSet K R) (hK : IsMinimalPreserver K K R) (q : Sym2 V) (hq : q ∈ R)
    (K' : SimpleGraph V) (hK' : IsPreserver K K' (R.erase q)) :
    (∀ e ∈ K.edgeSet, essSet K R e ≠ {q} → e ∈ K'.edgeSet) ∧
    (numEdges K : ℤ) - (numEdges K' : ℤ) ≤ (privLen K R q : ℤ) := by
  classical
  have hedge : ∀ e ∈ K.edgeSet, essSet K R e ≠ {q} → e ∈ K'.edgeSet := by
    intro e he hne
    have hn := minimal_essential K R hR hK e he
    have hex : ∃ q' ∈ essSet K R e, q' ≠ q := by
      by_contra! hall
      apply hne
      exact Finset.eq_singleton_iff_unique_mem.mpr ⟨by
        obtain ⟨q',hq'⟩ := hn
        simpa [hall q' hq'] using hq', hall⟩
    obtain ⟨q', hq', hne'⟩ := hex
    obtain ⟨hr',hess⟩ := Finset.mem_filter.mp hq'
    exact essential_mem K K' (R.erase q) (fun s t hst => hR s t (Finset.mem_of_mem_erase hst))
      hK' q' e (Finset.mem_erase.mpr ⟨hne',hr'⟩) hess
  refine ⟨hedge, ?_⟩
  have hsub : edgesF K' ⊆ edgesF K := by
    intro e he
    simp only [edgesF, Finset.mem_filter, Finset.mem_univ, true_and] at *
    exact SimpleGraph.edgeSet_mono hK'.1 he
  have hprivate : edgesF K \ edgesF K' ⊆ privOf K R q := by
    intro e he
    obtain ⟨heK,heK'⟩ := Finset.mem_sdiff.mp he
    have heK0 : e ∈ K.edgeSet := (Finset.mem_filter.mp heK).2
    have hess : essSet K R e = {q} := by
      by_contra hn
      exact heK' (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hedge e heK0 hn⟩)
    exact Finset.mem_filter.mpr ⟨heK,hess⟩
  have hc := Finset.card_le_card hprivate
  have hd := Finset.card_sdiff_add_card_eq_card hsub
  change ((edgesF K).card : ℤ) - ((edgesF K').card : ℤ) ≤ ((privOf K R q).card : ℤ)
  omega
