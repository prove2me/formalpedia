-- Prove2me | solution 1 for CountingLLL.DetCount.lemma_3_2
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T03:29:54.523237+00:00
-- url     : https://prove2.me/submissions/f831fd8b-7e12-4d48-bf1a-cec27a3b8e3f

import Definitions.Def_CountingLLL_DetCount_Expansion

set_option autoImplicit false

namespace CountingLLL.DetCount
open CSP

private theorem step_subset (Φ : CSP) (E D : Finset (Fin Φ.m))
    (st : Finset (Fin Φ.m) × Finset (Fin Φ.m)) :
    st.1 ⊆ (Φ.treeStep E D st).1 ∧ st.2 ⊆ (Φ.treeStep E D st).2 := by
  classical
  unfold CSP.treeStep
  dsimp only
  split_ifs <;> simp_all [Finset.subset_insert]

private theorem step_inv (Φ : CSP) (E D : Finset (Fin Φ.m))
    (st : Finset (Fin Φ.m) × Finset (Fin Φ.m))
    (ha : st.1 ⊆ D) (hr : st.2 ⊆ E \ D) :
    (Φ.treeStep E D st).1 ⊆ D ∧ (Φ.treeStep E D st).2 ⊆ E \ D := by
  classical
  unfold CSP.treeStep
  dsimp only
  split_ifs with h hD
  · simp only [Prod.fst, Prod.snd, Finset.insert_subset_iff]
    exact ⟨⟨hD, ha⟩, hr⟩
  · simp only [Prod.fst, Prod.snd, Finset.insert_subset_iff]
    refine ⟨ha, ⟨?_, hr⟩⟩
    exact Finset.mem_sdiff.mpr ⟨(Finset.mem_filter.mp (Finset.min'_mem _ h)).1, hD⟩
  · exact ⟨ha, hr⟩

private theorem run_inv (Φ : CSP) (E D : Finset (Fin Φ.m))
    (st : Finset (Fin Φ.m) × Finset (Fin Φ.m))
    (ha : st.1 ⊆ D) (hr : st.2 ⊆ E \ D) (n : ℕ) :
    ((Φ.treeStep E D)^[n] st).1 ⊆ D ∧ ((Φ.treeStep E D)^[n] st).2 ⊆ E \ D := by
  induction n with
  | zero => simpa using And.intro ha hr
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact step_inv Φ E D _ ih.1 ih.2

private theorem run_monotone (Φ : CSP) (E D : Finset (Fin Φ.m))
    (st : Finset (Fin Φ.m) × Finset (Fin Φ.m)) (n : ℕ) :
    st.1 ⊆ ((Φ.treeStep E D)^[n] st).1 ∧ st.2 ⊆ ((Φ.treeStep E D)^[n] st).2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact ⟨ih.1.trans (step_subset Φ E D _).1, ih.2.trans (step_subset Φ E D _).2⟩

private theorem distSet_mem_zero {V : Type} (G : SimpleGraph V) (S : Finset V) (v : V)
    (hv : v ∈ S) : distSet G v S = 0 := by
  apply le_antisymm
  · exact (Finset.inf_le hv).trans_eq SimpleGraph.edist_self
  · exact bot_le

private theorem step_active_growth (Φ : CSP) (E D : Finset (Fin Φ.m))
    (st : Finset (Fin Φ.m) × Finset (Fin Φ.m))
    (h : (E.filter (fun c => c ∉ st.2 ∧ distSet (Φ.depGraph E) c st.1 = 2)).Nonempty) :
    (st.1 ∪ st.2).card < (((Φ.treeStep E D st).1) ∪ ((Φ.treeStep E D st).2)).card := by
  classical
  let cand := E.filter (fun c => c ∉ st.2 ∧ distSet (Φ.depGraph E) c st.1 = 2)
  let c := cand.min' h
  have hc : c ∈ cand := Finset.min'_mem cand h
  have hmem := Finset.mem_filter.mp hc
  have hn1 : c ∉ st.1 := by
    intro hc1
    have hz := distSet_mem_zero (Φ.depGraph E) st.1 c hc1
    rw [hmem.2.2] at hz
    norm_num at hz
  have hn2 : c ∉ st.2 := hmem.2.1
  have hn : c ∉ st.1 ∪ st.2 := by simp [hn1, hn2]
  unfold CSP.treeStep
  dsimp only
  simp only [dif_pos h]
  split_ifs with hd
  · simp only [Prod.fst, Prod.snd, Finset.insert_union]
    rw [Finset.card_insert_of_notMem hn]
    omega
  · simp only [Prod.fst, Prod.snd, Finset.union_insert]
    rw [Finset.card_insert_of_notMem hn]
    omega

private def Active (Φ : CSP) (E : Finset (Fin Φ.m))
    (st : Finset (Fin Φ.m) × Finset (Fin Φ.m)) : Prop :=
  (E.filter (fun c => c ∉ st.2 ∧ distSet (Φ.depGraph E) c st.1 = 2)).Nonempty

private theorem step_inactive (Φ : CSP) (E D : Finset (Fin Φ.m))
    (st : Finset (Fin Φ.m) × Finset (Fin Φ.m)) (h : ¬ Active Φ E st) :
    Φ.treeStep E D st = st := by
  classical
  unfold Active at h
  simpa only [CSP.treeStep, dif_neg h]

private theorem active_iterate_growth (Φ : CSP) (E D : Finset (Fin Φ.m))
    (st : Finset (Fin Φ.m) × Finset (Fin Φ.m)) (n : ℕ)
    (h : Active Φ E ((Φ.treeStep E D)^[n] st)) :
    (st.1 ∪ st.2).card + n ≤
      (((Φ.treeStep E D)^[n] st).1 ∪ ((Φ.treeStep E D)^[n] st).2).card := by
  induction n with
  | zero => simp
  | succ n ih =>
    let prev := (Φ.treeStep E D)^[n] st
    have hp : Active Φ E prev := by
      by_contra hn
      have he := step_inactive Φ E D prev hn
      rw [Function.iterate_succ_apply', he] at h
      exact hn h
    have hi := ih hp
    have hs := step_active_growth Φ E D prev hp
    dsimp [prev] at hs
    rw [Function.iterate_succ_apply']
    omega

private theorem treeRun_terminal (Φ : CSP) (E D : Finset (Fin Φ.m)) (c₀ : Fin Φ.m)
    (hc : c₀ ∈ D) (hDE : D ⊆ E) : ¬ Active Φ E (Φ.treeRun E c₀ D) := by
  classical
  intro h
  have hg := active_iterate_growth Φ E D ({c₀}, ∅) E.card h
  have hi := run_inv Φ E D ({c₀}, ∅) (by simpa using hc) (by simp) E.card
  have hs : (Φ.treeRun E c₀ D).1 ∪ (Φ.treeRun E c₀ D).2 ⊆ E :=
    Finset.union_subset (hi.1.trans hDE) (hi.2.trans (Finset.sdiff_subset))
  have hb := Finset.card_le_card hs
  simp only [Finset.union_empty, Finset.card_singleton] at hg
  change 1 + E.card ≤ ((Φ.treeRun E c₀ D).1 ∪ (Φ.treeRun E c₀ D).2).card at hg
  omega

private theorem dist_two_neighbors {V : Type} (G : SimpleGraph V) (T : Finset V) (v : V)
    (h : distSet G v T = 2) :
    (∀ w ∈ T, v ≠ w ∧ ¬G.Adj v w) ∧ ∃ w ∈ T, (square G).Adj v w := by
  classical
  have hlo : ∀ w ∈ T, (2 : ℕ∞) ≤ G.edist v w := by
    intro w hw
    have hh := Finset.inf_le (f := fun w => G.edist v w) hw
    rw [← h]
    exact hh
  constructor
  · intro w hw
    have hh := hlo w hw
    constructor
    · intro he
      subst w
      simp only [SimpleGraph.edist_self] at hh
      norm_num at hh
    · intro ha
      rw [← SimpleGraph.edist_eq_one_iff_adj] at ha
      rw [ha] at hh
      norm_num at hh
  · have hex : ∃ w ∈ T, G.edist v w ≤ 2 := by
      apply (Finset.inf_le_iff (ENat.natCast_lt_top 2)).mp
      change distSet G v T ≤ 2
      rw [h]
    obtain ⟨w, hw, hle⟩ := hex
    refine ⟨w, hw, ?_, hle⟩
    intro he
    subst w
    simp only [SimpleGraph.edist_self] at hle ⊢
    have hh := hlo v hw
    simp only [SimpleGraph.edist_self] at hh
    norm_num at hh

private theorem twoTree_insert {V : Type} [DecidableEq V] (G : SimpleGraph V) (T : Finset V) (v : V)
    (ht : IsTwoTree G T) (h : distSet G v T = 2) : IsTwoTree G (insert v T) := by
  classical
  obtain ⟨hn, ⟨w, hw, hadj⟩⟩ := dist_two_neighbors G T v h
  unfold IsTwoTree at ht ⊢
  constructor
  · rw [SimpleGraph.isIndepSet_iff] at ht ⊢
    intro a ha b hb hab
    simp only [Finset.coe_insert, Set.mem_insert_iff] at ha hb
    rcases ha with rfl | ha
    · rcases hb with rfl | hb
      · exact False.elim (hab rfl)
      · exact (hn b hb).2
    · rcases hb with rfl | hb
      · exact fun hab' => (hn a ha).2 hab'.symm
      · exact ht.1 ha hb hab
  · have hs : ((square G).induce ({v} : Set V)).Preconnected := by
      exact SimpleGraph.Preconnected.of_subsingleton
    have hconn := SimpleGraph.connected_induce_union ht.2.preconnected hs hw (by simp) hadj.symm
    have heq : (↑(insert v T) : Set V) = (↑T : Set V) ∪ {v} := by
      ext x
      simp [or_comm]
    rw [heq]
    exact hconn

private theorem twoTree_singleton {V : Type} [DecidableEq V] (G : SimpleGraph V) (v : V) :
    IsTwoTree G {v} := by
  constructor
  · rw [SimpleGraph.isIndepSet_iff]
    simp [Set.Pairwise]
  · have heq : (({v} : Finset V) : Set V) = {v} := by ext x; simp
    rw [heq, SimpleGraph.connected_iff]
    constructor
    · exact SimpleGraph.Preconnected.of_subsingleton
    · exact ⟨⟨v, by simp⟩⟩

private theorem step_tree (Φ : CSP) (E D : Finset (Fin Φ.m))
    (st : Finset (Fin Φ.m) × Finset (Fin Φ.m))
    (ht : IsTwoTree (Φ.depGraph E) st.1) :
    IsTwoTree (Φ.depGraph E) (Φ.treeStep E D st).1 := by
  classical
  unfold CSP.treeStep
  dsimp only
  split_ifs with hc hd
  · apply twoTree_insert _ _ _ ht
    exact (Finset.mem_filter.mp (Finset.min'_mem _ hc)).2.2
  · exact ht
  · exact ht

private theorem iterate_tree (Φ : CSP) (E D : Finset (Fin Φ.m))
    (st : Finset (Fin Φ.m) × Finset (Fin Φ.m))
    (ht : IsTwoTree (Φ.depGraph E) st.1) (n : ℕ) :
    IsTwoTree (Φ.depGraph E) ((Φ.treeStep E D)^[n] st).1 := by
  induction n with
  | zero => simpa using ht
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact step_tree Φ E D _ ih

private theorem tree_output (Φ : CSP) (E : Finset (Fin Φ.m)) (c₀ : Fin Φ.m)
    (D : Finset (Fin Φ.m)) (hc : c₀ ∈ D) (hDE : D ⊆ E) :
    Φ.Tree E c₀ D ∈ Φ.twoTrees E c₀ := by
  classical
  have hi := run_inv Φ E D ({c₀}, ∅) (by simpa using hc) (by simp) E.card
  have hm := run_monotone Φ E D ({c₀}, ∅) E.card
  have ht := iterate_tree Φ E D ({c₀}, ∅) (twoTree_singleton (Φ.depGraph E) c₀) E.card
  unfold CSP.twoTrees
  simp only [Finset.mem_filter, Finset.mem_powerset]
  refine ⟨?_, ?_, ?_⟩
  · exact hi.1.trans hDE
  · exact hm.1 (by simp)
  · exact ht

private theorem twoTree_crossing_distance {V : Type} [DecidableEq V] (G : SimpleGraph V)
    (T U : Finset V) (v : V) (ht : IsTwoTree G T) (hUT : U ⊆ T) (hvT : v ∈ T)
    (hvU : v ∉ U) (hw : ∃ w ∈ U, (square G).Adj v w) : distSet G v U = 2 := by
  classical
  apply le_antisymm
  · obtain ⟨w, hw, hadj⟩ := hw
    exact (Finset.inf_le (f := fun w => G.edist v w) hw).trans hadj.2
  · apply Finset.le_inf
    intro w hw
    have hne : v ≠ w := by intro he; subst w; exact hvU hw
    have hna : ¬ G.Adj v w := ht.1 hvT (hUT hw) hne
    have hnle : ¬ G.edist v w ≤ 1 := by
      rw [SimpleGraph.edist_le_one_iff_adj_or_eq]
      exact not_or.mpr ⟨hna, hne⟩
    have hlt : (1 : ℕ∞) < G.edist v w := lt_of_not_ge hnle
    exact (ENat.natCast_add_one_le_iff (m := 1)).2 hlt

private theorem tree_fixed (Φ : CSP) (E : Finset (Fin Φ.m)) (c₀ : Fin Φ.m)
    (T : Finset (Fin Φ.m)) (hT : T ∈ Φ.twoTrees E c₀) : Φ.Tree E c₀ T = T := by
  classical
  have hT' : T ⊆ E ∧ c₀ ∈ T ∧ IsTwoTree (Φ.depGraph E) T := by
    simpa [CSP.twoTrees] using hT
  let st := Φ.treeRun E c₀ T
  have hi := run_inv Φ E T ({c₀}, ∅) (by simpa using hT'.2.1) (by simp) E.card
  have hm := run_monotone Φ E T ({c₀}, ∅) E.card
  have hsub : st.1 ⊆ T := hi.1
  have hroot : c₀ ∈ st.1 := hm.1 (by simp)
  have hterm : ¬ Active Φ E st := treeRun_terminal Φ E T c₀ hT'.2.1 hT'.1
  have hclosed : ∀ a ∈ st.1, ∀ b ∈ T, (square (Φ.depGraph E)).Adj a b → b ∈ st.1 := by
    intro a ha b hb hab
    by_contra hnot
    have hdist := twoTree_crossing_distance (Φ.depGraph E) T st.1 b hT'.2.2 hsub hb hnot
      ⟨a, ha, hab.symm⟩
    have hnotR : b ∉ st.2 := by
      intro hbR
      exact (Finset.mem_sdiff.mp (hi.2 hbR)).2 hb
    apply hterm
    exact ⟨b, Finset.mem_filter.mpr ⟨hT'.1 hb, hnotR, hdist⟩⟩
  have hrev : T ⊆ st.1 := by
    intro v hv
    have hprop : ∀ (x : ↥(T : Set (Fin Φ.m))), x.1 ∈ st.1 := by
      intro x
      have hx := hT'.2.2.2.preconnected ⟨c₀, hT'.2.1⟩ x
      rw [SimpleGraph.reachable_iff_reflTransGen] at hx
      induction hx with
      | refl => exact hroot
      | tail hreach hedge ih =>
        exact hclosed _ ih _ (by simpa using hedge.2.property) hedge
    exact hprop ⟨v, hv⟩
  exact Finset.Subset.antisymm hsub hrev

end CountingLLL.DetCount

open CountingLLL.DetCount
open CountingLLL.DetCount.CSP

theorem solution (Φ : CSP) (E : Finset (Fin Φ.m)) (c₀ : Fin Φ.m) :
    (∀ D : Finset (Fin Φ.m), c₀ ∈ D → D ⊆ E → Φ.Tree E c₀ D ∈ Φ.twoTrees E c₀) ∧
    (∀ T ∈ Φ.twoTrees E c₀, Φ.Tree E c₀ T = T) := by
  exact ⟨fun D hc hDE => tree_output Φ E c₀ D hc hDE,
    fun T hT => tree_fixed Φ E c₀ T hT⟩

