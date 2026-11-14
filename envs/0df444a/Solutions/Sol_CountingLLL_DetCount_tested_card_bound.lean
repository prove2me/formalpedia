-- Prove2me | solution 1 for CountingLLL.DetCount.tested_card_bound
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T06:16:51.434206+00:00
-- url     : https://prove2.me/submissions/6b1e01f8-0344-46ec-9668-b38e9cd4de9d

import Theorems.Thm_CountingLLL_DetCount_lemma_3_2

set_option autoImplicit false
open scoped Classical

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

private theorem inf_two_has_witness {V : Type} (G : SimpleGraph V) (S : Finset V) (v : V)
    (h : distSet G v S = 2) : ∃ w ∈ S, G.edist v w = 2 := by
  classical
  have hw : ∃ w ∈ S, G.edist v w ≤ 2 := by
    apply (Finset.inf_le_iff (ENat.natCast_lt_top 2)).mp
    change distSet G v S ≤ 2
    rw [h]
  obtain ⟨w, hw, hle⟩ := hw
  refine ⟨w, hw, le_antisymm hle ?_⟩
  have hlow := Finset.inf_le (f := fun w => G.edist v w) hw
  change distSet G v S ≤ G.edist v w at hlow
  rw [h] at hlow
  exact hlow

private def RejectWitness (Φ : CSP) (E : Finset (Fin Φ.m))
    (st : Finset (Fin Φ.m) × Finset (Fin Φ.m)) : Prop :=
  ∀ c ∈ st.2, ∃ t ∈ st.1, (Φ.depGraph E).edist c t = 2

private theorem witness_step (Φ : CSP) (E D : Finset (Fin Φ.m))
    (st : Finset (Fin Φ.m) × Finset (Fin Φ.m)) (h : RejectWitness Φ E st) :
    RejectWitness Φ E (Φ.treeStep E D st) := by
  classical
  unfold CSP.treeStep
  dsimp only
  split_ifs with hc hd
  · intro c hcR
    obtain ⟨t, ht, he⟩ := h c hcR
    exact ⟨t, Finset.mem_insert_of_mem ht, he⟩
  · intro c hcR
    rcases Finset.mem_insert.mp hcR with hnew | hold
    · subst c
      exact inf_two_has_witness (Φ.depGraph E) st.1 _ (Finset.mem_filter.mp (Finset.min'_mem _ hc)).2.2
    · exact h c hold
  · exact h

private theorem witness_run (Φ : CSP) (E D : Finset (Fin Φ.m)) (r : Fin Φ.m) :
    RejectWitness Φ E (Φ.treeRun E r D) := by
  have h : ∀ n, RejectWitness Φ E ((Φ.treeStep E D)^[n] ({r}, ∅)) := by
    intro n
    induction n with
    | zero => simp [RejectWitness]
    | succ n ih => rw [Function.iterate_succ_apply']; exact witness_step Φ E D _ ih
  exact h E.card

private theorem nbr_subset_univ (Φ : CSP) (E : Finset (Fin Φ.m)) (v : Fin Φ.m) :
    Φ.nbr E v ⊆ Φ.nbr Finset.univ v := by
  classical
  intro x hx
  have hx' := Finset.mem_filter.mp hx
  apply Finset.mem_filter.mpr
  exact ⟨Finset.mem_univ _, hx'.2⟩

private theorem nbr_card_bound (Φ : CSP) (E : Finset (Fin Φ.m)) (v : Fin Φ.m) :
    (Φ.nbr E v).card ≤ Φ.Dmax := by
  classical
  apply (Finset.card_le_card (nbr_subset_univ Φ E v)).trans
  unfold CSP.Dmax CSP.Dsub
  exact Finset.le_sup (f := fun c => (Φ.nbr Finset.univ c).card) (Finset.mem_univ v)

private theorem adj_nbr (Φ : CSP) (E : Finset (Fin Φ.m)) {a b : Fin Φ.m}
    (h : (Φ.depGraph E).Adj a b) : b ∈ Φ.nbr E a := by
  classical
  apply Finset.mem_filter.mpr
  exact ⟨h.2.1, h.2.2.1.symm, h.2.2.2⟩

private theorem nbr_two_card (Φ : CSP) (E : Finset (Fin Φ.m)) (v : Fin Φ.m) :
    ((Φ.nbr E v).biUnion (Φ.nbr E)).card ≤ Φ.Dmax^2 := by
  classical
  calc
    _ ≤ ∑ w ∈ Φ.nbr E v, (Φ.nbr E w).card := Finset.card_biUnion_le
    _ ≤ ∑ _w ∈ Φ.nbr E v, Φ.Dmax := by
      apply Finset.sum_le_sum
      intro w hw
      exact nbr_card_bound Φ E w
    _ = (Φ.nbr E v).card * Φ.Dmax := by simp [Finset.sum_const, nsmul_eq_mul]
    _ ≤ Φ.Dmax^2 := by
      have h := nbr_card_bound Φ E v
      nlinarith


private def TestedWitness (Φ : CSP) (E : Finset (Fin Φ.m)) (r : Fin Φ.m)
    (st : Finset (Fin Φ.m) × Finset (Fin Φ.m)) : Prop :=
  ∀ c, ((c ∈ st.1 ∧ c ≠ r) ∨ c ∈ st.2) →
    ∃ t ∈ st.1, (Φ.depGraph E).edist c t = 2

private theorem tested_witness_step (Φ : CSP) (E D : Finset (Fin Φ.m)) (r : Fin Φ.m)
    (st : Finset (Fin Φ.m) × Finset (Fin Φ.m)) (h : TestedWitness Φ E r st) :
    TestedWitness Φ E r (Φ.treeStep E D st) := by
  classical
  unfold CSP.treeStep
  dsimp only
  split_ifs with hc hd
  · intro c hmem
    rcases hmem with ⟨hcT,hcr⟩ | hcR
    · rcases Finset.mem_insert.mp hcT with hnew | hold
      · subst c
        obtain ⟨t, ht, he⟩ := inf_two_has_witness (Φ.depGraph E) st.1 _
          (Finset.mem_filter.mp (Finset.min'_mem _ hc)).2.2
        exact ⟨t, Finset.mem_insert_of_mem ht, he⟩
      · obtain ⟨t, ht, he⟩ := h c (Or.inl ⟨hold,hcr⟩)
        exact ⟨t, Finset.mem_insert_of_mem ht, he⟩
    · obtain ⟨t, ht, he⟩ := h c (Or.inr hcR)
      exact ⟨t, Finset.mem_insert_of_mem ht, he⟩
  · intro c hmem
    rcases hmem with hcT | hcR
    · exact h c (Or.inl hcT)
    · rcases Finset.mem_insert.mp hcR with hnew | hold
      · subst c
        exact inf_two_has_witness (Φ.depGraph E) st.1 _
          (Finset.mem_filter.mp (Finset.min'_mem _ hc)).2.2
      · exact h c (Or.inr hold)
  · exact h

private theorem tested_witness_run (Φ : CSP) (E D : Finset (Fin Φ.m)) (r : Fin Φ.m) :
    TestedWitness Φ E r (Φ.treeRun E r D) := by
  have h : ∀ n, TestedWitness Φ E r ((Φ.treeStep E D)^[n] ({r}, ∅)) := by
    intro n
    induction n with
    | zero => simp [TestedWitness]
    | succ n ih => rw [Function.iterate_succ_apply']; exact tested_witness_step Φ E D r _ ih
  exact h E.card

/-- The total number of tested non-root vertices is at most D² times tree size. -/
theorem tested_card_local (Φ : CSP) (E T : Finset (Fin Φ.m)) (r : Fin Φ.m)
    (hT : T ∈ Φ.twoTrees E r) :
    (Φ.rest E r T).card ≤ Φ.Dmax^2 * T.card := by
  classical
  have hfix := (lemma_3_2 Φ E r).2 T hT
  have hwit := tested_witness_run Φ E T r
  have hsub : Φ.rest E r T ⊆ T.biUnion (fun t => (Φ.nbr E t).biUnion (Φ.nbr E)) := by
    intro c hc
    have hcE : c ∈ E := (Finset.mem_sdiff.mp hc).1
    have hcnot : c ∉ ({r} ∪ Φ.free E r T) := (Finset.mem_sdiff.mp hc).2
    have hcr : c ≠ r := by
      intro heq
      subst c
      exact hcnot (Finset.mem_union_left _ (Finset.mem_singleton_self _))
    have hTorR : c ∈ T ∨ c ∈ Φ.rejected E r T := by
      by_contra hn
      have hfree : c ∈ Φ.free E r T := by
        apply Finset.mem_sdiff.mpr
        exact ⟨hcE, by simpa [Finset.mem_union] using hn⟩
      exact hcnot (Finset.mem_union_right _ hfree)
    have hw : ∃ t ∈ (Φ.treeRun E r T).1, (Φ.depGraph E).edist c t = 2 := by
      apply hwit c
      rcases hTorR with ht | hR
      · left
        constructor
        · change c ∈ Φ.Tree E r T
          rwa [hfix]
        · exact hcr
      · exact Or.inr hR
    obtain ⟨t, ht, he⟩ := hw
    have ht' : t ∈ T := by change t ∈ Φ.Tree E r T at ht; rwa [hfix] at ht
    obtain ⟨_, _, ⟨w, hpath⟩⟩ := SimpleGraph.edist_eq_two_iff.mp he
    apply Finset.mem_biUnion.mpr
    refine ⟨t, ht', ?_⟩
    apply Finset.mem_biUnion.mpr
    exact ⟨w, adj_nbr Φ E hpath.2, adj_nbr Φ E hpath.1.symm⟩
  calc
    _ ≤ (T.biUnion (fun t => (Φ.nbr E t).biUnion (Φ.nbr E))).card := Finset.card_le_card hsub
    _ ≤ ∑ t ∈ T, ((Φ.nbr E t).biUnion (Φ.nbr E)).card := Finset.card_biUnion_le
    _ ≤ ∑ _t ∈ T, Φ.Dmax^2 := by
      apply Finset.sum_le_sum
      intro t ht
      exact nbr_two_card Φ E t
    _ = Φ.Dmax^2 * T.card := by simp [Finset.sum_const, nsmul_eq_mul, Nat.mul_comm]

end CountingLLL.DetCount

open CountingLLL.DetCount

theorem solution (Φ : CSP) (E T : Finset (Fin Φ.m)) (r : Fin Φ.m)
    (hT : T ∈ Φ.twoTrees E r) :
    (Φ.rest E r T).card ≤ Φ.Dmax^2 * T.card :=
  tested_card_local Φ E T r hT
