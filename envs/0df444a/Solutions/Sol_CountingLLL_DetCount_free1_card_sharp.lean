-- Prove2me | solution 1 for CountingLLL.DetCount.free1_card_sharp
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T04:44:26.058604+00:00
-- url     : https://prove2.me/submissions/8a152462-a3be-4f3c-9b87-5ca8e4a0f491

import Definitions.Def_CountingLLL_DetCount_Expansion

set_option autoImplicit false
open CountingLLL.DetCount
open CountingLLL.DetCount.CSP
open scoped Classical

/-- Any proper nonempty part of a connected induced graph has a crossing edge. -/
private theorem connected_crossing {V : Type} [DecidableEq V] (G : SimpleGraph V)
    (T X : Finset V) (hX : X ⊆ T) (hne : X.Nonempty) (hproper : X ≠ T)
    (hconn : (G.induce (T : Set V)).Connected) :
    ∃ u ∈ X, ∃ v ∈ T \ X, G.Adj u v := by
  classical
  by_contra hnone
  have hclosed : ∀ u ∈ X, ∀ v ∈ T, G.Adj u v → v ∈ X := by
    intro u hu v hv huv
    by_contra hvX
    apply hnone
    exact ⟨u, hu, v, Finset.mem_sdiff.mpr ⟨hv, hvX⟩, huv⟩
  obtain ⟨u, hu⟩ := hne
  have hall : T ⊆ X := by
    intro v hv
    have hprop : ∀ x : ↥(T : Set V), x.1 ∈ X := by
      intro x
      have hx := hconn.preconnected ⟨u, hX hu⟩ x
      rw [SimpleGraph.reachable_iff_reflTransGen] at hx
      induction hx with
      | refl => exact hu
      | @tail b c _ hedge ih => exact hclosed _ ih _ c.property hedge
    exact hprop ⟨v, hv⟩
  exact hproper (Finset.Subset.antisymm hX hall)

/-- A connected family of finite sets has at most D new members at the first
vertex and at most D−1 at each subsequent vertex. -/
theorem connected_family_union_bound {V U : Type} [DecidableEq V] [DecidableEq U]
    (G : SimpleGraph V) (T : Finset V) (N : V → Finset U) (D : ℕ)
    (hconn : (G.induce (T : Set V)).Connected)
    (hsize : ∀ v ∈ T, (N v).card ≤ D)
    (hinter : ∀ u ∈ T, ∀ v ∈ T, G.Adj u v → ((N u) ∩ (N v)).Nonempty) :
    (T.biUnion N).card + T.card ≤ D*T.card + 1 := by
  classical
  have hne : T.Nonempty := by
    obtain ⟨v⟩ := hconn.nonempty
    exact ⟨v.1, v.2⟩
  have hgrow : ∀ n : ℕ, ∀ X : Finset V, X ⊆ T → X.Nonempty → T.card-X.card = n →
      (X.biUnion N).card + X.card ≤ D*X.card + 1 →
      (T.biUnion N).card + T.card ≤ D*T.card + 1 := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro X hXT hX hdiff hbound
      by_cases heq : X = T
      · simpa [heq] using hbound
      · obtain ⟨u, huX, v, hv, huv⟩ := connected_crossing G T X hXT hX heq hconn
        have hvT := (Finset.mem_sdiff.mp hv).1
        have hvX := (Finset.mem_sdiff.mp hv).2
        let Y := insert v X
        have hYT : Y ⊆ T := Finset.insert_subset hvT hXT
        have hYne : Y.Nonempty := ⟨v, Finset.mem_insert_self _ _⟩
        have hYcard : Y.card = X.card + 1 := Finset.card_insert_of_notMem hvX
        have hXY : X.card < T.card := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hXT, heq⟩)
        have hinter' : ((N v) ∩ (X.biUnion N)).Nonempty := by
          obtain ⟨z, hz⟩ := hinter u (hXT huX) v hvT huv
          have hz' := Finset.mem_inter.mp hz
          exact ⟨z, Finset.mem_inter.mpr ⟨hz'.2, Finset.mem_biUnion.mpr ⟨u, huX, hz'.1⟩⟩⟩
        have hintercard : 1 ≤ ((N v) ∩ (X.biUnion N)).card := Finset.card_pos.mpr hinter'
        have hunion := Finset.card_union_add_card_inter (N v) (X.biUnion N)
        have hnew : (Y.biUnion N).card + Y.card ≤ D*Y.card + 1 := by
          rw [show Y.biUnion N = N v ∪ X.biUnion N by simp [Y], hYcard]
          have hvsize := hsize v hvT
          nlinarith
        have hdecr : T.card - Y.card < n := by rw [hYcard] at *; omega
        exact ih (T.card-Y.card) hdecr Y hYT hYne rfl hnew
  obtain ⟨r, hr⟩ := hne
  apply hgrow (T.card - ({r} : Finset V).card) {r}
  · simpa using hr
  · exact ⟨r, by simp⟩
  · rfl
  · simpa using hsize r hr

private theorem adj_nbr (Φ : CSP) (E : Finset (Fin Φ.m)) {a b : Fin Φ.m}
    (h : (Φ.depGraph E).Adj a b) : b ∈ Φ.nbr E a := by
  classical
  apply Finset.mem_filter.mpr
  exact ⟨h.2.1, h.2.2.1.symm, h.2.2.2⟩

private theorem free1_subset_neighborhoods (Φ : CSP) (E T : Finset (Fin Φ.m)) (r : Fin Φ.m) :
    Φ.free1 E r T ⊆ T.biUnion (Φ.nbr E) := by
  classical
  intro c hc
  have hh := Finset.mem_filter.mp hc
  have hfree := Finset.mem_sdiff.mp hh.1
  have hnotT : c ∉ T := fun h => hfree.2 (Finset.mem_union_left _ h)
  have hle : distSet (Φ.depGraph E) c T ≤ 1 := hh.2.le
  obtain ⟨t, ht, hct⟩ := (Finset.inf_le_iff (ENat.natCast_lt_top 1)).mp hle
  have hne : c ≠ t := fun h => hnotT (h ▸ ht)
  have hdist : (Φ.depGraph E).edist c t = 1 := by
    rcases Order.le_one_iff.mp hct with h0 | h1
    · exact False.elim (hne (SimpleGraph.edist_eq_zero_iff.mp h0))
    · exact h1
  have hadj := SimpleGraph.edist_eq_one_iff_adj.mp hdist
  apply Finset.mem_biUnion.mpr
  exact ⟨t, ht, adj_nbr Φ E hadj.symm⟩

/-- The sharp graph-counting clause in Lemma 4.2, with the degree of the subfamily. -/
theorem solution (Φ : CSP) (E T : Finset (Fin Φ.m)) (r : Fin Φ.m)
    (hT : T ∈ Φ.twoTrees E r) :
    ((Φ.free1 E r T).card : ℤ) ≤ ((Φ.Dsub E : ℤ)-1) * T.card + 1 := by
  classical
  have hT' : T ⊆ E ∧ r ∈ T ∧ IsTwoTree (Φ.depGraph E) T := by
    simpa [CSP.twoTrees] using hT
  have hsize : ∀ v ∈ T, (Φ.nbr E v).card ≤ Φ.Dsub E := by
    intro v hv
    unfold CSP.Dsub
    exact Finset.le_sup (f := fun c => (Φ.nbr E c).card) (hT'.1 hv)
  have hinter : ∀ u ∈ T, ∀ v ∈ T, (square (Φ.depGraph E)).Adj u v →
      (Φ.nbr E u ∩ Φ.nbr E v).Nonempty := by
    intro u hu v hv hsq
    have hind : ¬ (Φ.depGraph E).Adj u v := hT'.2.2.1 hu hv hsq.1
    have hnle : ¬ (Φ.depGraph E).edist u v ≤ 1 := by
      rw [SimpleGraph.edist_le_one_iff_adj_or_eq]
      exact not_or.mpr ⟨hind, hsq.1⟩
    have hge : (2 : ℕ∞) ≤ (Φ.depGraph E).edist u v :=
      (ENat.natCast_add_one_le_iff (m := 1)).2 (lt_of_not_ge hnle)
    have heq : (Φ.depGraph E).edist u v = 2 := le_antisymm hsq.2 hge
    obtain ⟨_, _, ⟨w, hw⟩⟩ := SimpleGraph.edist_eq_two_iff.mp heq
    exact ⟨w, Finset.mem_inter.mpr ⟨adj_nbr Φ E hw.1, adj_nbr Φ E hw.2⟩⟩
  have hbound := connected_family_union_bound (square (Φ.depGraph E)) T (Φ.nbr E) (Φ.Dsub E)
    hT'.2.2.2 hsize hinter
  have hsub := Finset.card_le_card (free1_subset_neighborhoods Φ E T r)
  have hZ : ((Φ.free1 E r T).card : ℤ) + T.card ≤ (Φ.Dsub E : ℤ)*T.card + 1 := by
    exact_mod_cast (le_trans (Nat.add_le_add_right hsub _) hbound)
  nlinarith
