-- Prove2me | solution 1 for CountingLLL.DetCount.lemma_3_4
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T03:36:33.599735+00:00
-- url     : https://prove2.me/submissions/9f0b3124-9ec3-46c1-9f26-7fe582f6859e

import Theorems.Thm_CountingLLL_DetCount_lemma_3_2

set_option autoImplicit false

namespace CountingLLL.DetCount
open CSP

private theorem step_mono (Φ : CSP) (E D : Finset (Fin Φ.m))
    (st : Finset (Fin Φ.m) × Finset (Fin Φ.m)) :
    st.1 ⊆ (Φ.treeStep E D st).1 ∧ st.2 ⊆ (Φ.treeStep E D st).2 := by
  classical
  unfold CSP.treeStep
  dsimp only
  split_ifs <;> simp_all [Finset.subset_insert]

private theorem iterate_mono (Φ : CSP) (E D : Finset (Fin Φ.m))
    (st : Finset (Fin Φ.m) × Finset (Fin Φ.m)) (n : ℕ) :
    st.1 ⊆ ((Φ.treeStep E D)^[n] st).1 ∧ st.2 ⊆ ((Φ.treeStep E D)^[n] st).2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact ⟨ih.1.trans (step_mono Φ E D _).1, ih.2.trans (step_mono Φ E D _).2⟩

private theorem iterate_mono_le (Φ : CSP) (E D : Finset (Fin Φ.m))
    (st : Finset (Fin Φ.m) × Finset (Fin Φ.m)) (i n : ℕ) (h : i ≤ n) :
    ((Φ.treeStep E D)^[i] st).1 ⊆ ((Φ.treeStep E D)^[n] st).1 ∧
    ((Φ.treeStep E D)^[i] st).2 ⊆ ((Φ.treeStep E D)^[n] st).2 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [Nat.add_comm i k, Function.iterate_add_apply]
  exact iterate_mono Φ E D _ k

private theorem step_subset_input (Φ : CSP) (E D : Finset (Fin Φ.m))
    (st : Finset (Fin Φ.m) × Finset (Fin Φ.m)) (hs : st.1 ⊆ D) :
    (Φ.treeStep E D st).1 ⊆ D := by
  classical
  unfold CSP.treeStep
  dsimp only
  split_ifs with hc hd
  · simpa only [Finset.insert_subset_iff] using And.intro hd hs
  · exact hs
  · exact hs

private theorem run_subset_input (Φ : CSP) (E D : Finset (Fin Φ.m))
    (c₀ : Fin Φ.m) (hc : c₀ ∈ D) : Φ.Tree E c₀ D ⊆ D := by
  have h : ∀ n, ((Φ.treeStep E D)^[n] ({c₀}, ∅)).1 ⊆ D := by
    intro n
    induction n with
    | zero => simpa using hc
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact step_subset_input Φ E D _ ih
  exact h E.card

private theorem step_agree (Φ : CSP) (E A B : Finset (Fin Φ.m))
    (st : Finset (Fin Φ.m) × Finset (Fin Φ.m))
    (h : ∀ hc : (E.filter (fun c => c ∉ st.2 ∧ distSet (Φ.depGraph E) c st.1 = 2)).Nonempty,
      (E.filter (fun c => c ∉ st.2 ∧ distSet (Φ.depGraph E) c st.1 = 2)).min' hc ∈ A ↔
      (E.filter (fun c => c ∉ st.2 ∧ distSet (Φ.depGraph E) c st.1 = 2)).min' hc ∈ B) : Φ.treeStep E A st = Φ.treeStep E B st := by
  classical
  unfold CSP.treeStep
  dsimp only
  split_ifs with hc ha hb <;> try rfl
  all_goals exfalso
  all_goals have hh := h hc
  all_goals tauto

private theorem chosen_accepted (Φ : CSP) (E A : Finset (Fin Φ.m))
    (st : Finset (Fin Φ.m) × Finset (Fin Φ.m))
    (hc : (E.filter (fun c => c ∉ st.2 ∧ distSet (Φ.depGraph E) c st.1 = 2)).Nonempty)
    (ha : (E.filter (fun c => c ∉ st.2 ∧ distSet (Φ.depGraph E) c st.1 = 2)).min' hc ∈ A) :
    (E.filter (fun c => c ∉ st.2 ∧ distSet (Φ.depGraph E) c st.1 = 2)).min' hc ∈
      (Φ.treeStep E A st).1 := by
  classical
  simp [CSP.treeStep, hc, ha]

private theorem chosen_rejected (Φ : CSP) (E A : Finset (Fin Φ.m))
    (st : Finset (Fin Φ.m) × Finset (Fin Φ.m))
    (hc : (E.filter (fun c => c ∉ st.2 ∧ distSet (Φ.depGraph E) c st.1 = 2)).Nonempty)
    (ha : (E.filter (fun c => c ∉ st.2 ∧ distSet (Φ.depGraph E) c st.1 = 2)).min' hc ∉ A) :
    (E.filter (fun c => c ∉ st.2 ∧ distSet (Φ.depGraph E) c st.1 = 2)).min' hc ∈
      (Φ.treeStep E A st).2 := by
  classical
  simp [CSP.treeStep, hc, ha]

private theorem sync_of_accepted (Φ : CSP) (E A B : Finset (Fin Φ.m)) (c₀ : Fin Φ.m) (N : ℕ)
    (hBA : B ⊆ A)
    (hfinal : ((Φ.treeStep E A)^[N] ({c₀}, ∅)).1 ⊆ B) :
    ∀ n ≤ N, (Φ.treeStep E A)^[n] ({c₀}, ∅) = (Φ.treeStep E B)^[n] ({c₀}, ∅) := by
  intro n hn
  induction n with
  | zero => rfl
  | succ n ih =>
    have heq := ih (by omega)
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← heq]
    apply step_agree
    intro hc
    constructor
    · intro ha
      apply hfinal
      apply (iterate_mono_le Φ E A ({c₀}, ∅) (n+1) N hn).1
      rw [Function.iterate_succ_apply']
      exact chosen_accepted Φ E A _ hc ha
    · exact fun h => hBA h

private theorem sync_of_rejected (Φ : CSP) (E A B : Finset (Fin Φ.m)) (c₀ : Fin Φ.m) (N : ℕ)
    (hAB : A ⊆ B)
    (hfinal : ∀ c ∈ B, c ∉ ((Φ.treeStep E A)^[N] ({c₀}, ∅)).2) :
    ∀ n ≤ N, (Φ.treeStep E A)^[n] ({c₀}, ∅) = (Φ.treeStep E B)^[n] ({c₀}, ∅) := by
  intro n hn
  induction n with
  | zero => rfl
  | succ n ih =>
    have heq := ih (by omega)
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← heq]
    apply step_agree
    intro hc
    constructor
    · exact fun h => hAB h
    · intro hb
      by_contra ha
      apply hfinal _ hb
      apply (iterate_mono_le Φ E A ({c₀}, ∅) (n+1) N hn).2
      rw [Function.iterate_succ_apply']
      exact chosen_rejected Φ E A _ hc ha

private theorem step_rejected_subset (Φ : CSP) (E D : Finset (Fin Φ.m))
    (st : Finset (Fin Φ.m) × Finset (Fin Φ.m)) (hs : st.2 ⊆ E \ D) :
    (Φ.treeStep E D st).2 ⊆ E \ D := by
  classical
  unfold CSP.treeStep
  dsimp only
  split_ifs with hc hd
  · exact hs
  · simp only [Finset.insert_subset_iff]
    exact ⟨Finset.mem_sdiff.mpr ⟨(Finset.mem_filter.mp (Finset.min'_mem _ hc)).1, hd⟩, hs⟩
  · exact hs

private theorem rejected_subset (Φ : CSP) (E D : Finset (Fin Φ.m)) (c₀ : Fin Φ.m) :
    (Φ.treeRun E c₀ D).2 ⊆ E \ D := by
  have h : ∀ n, ((Φ.treeStep E D)^[n] ({c₀}, ∅)).2 ⊆ E \ D := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact step_rejected_subset Φ E D _ ih
  exact h E.card

private theorem inversion (Φ : CSP) (E : Finset (Fin Φ.m)) (c₀ : Fin Φ.m) (hc₀ : c₀ ∈ E)
    (T : Finset (Fin Φ.m)) (hT : T ∈ Φ.twoTrees E c₀) :
    {D : Finset (Fin Φ.m) | D ⊆ E ∧ c₀ ∈ D ∧ Φ.Tree E c₀ D = T} =
      {D : Finset (Fin Φ.m) | ∃ S ⊆ Φ.free E c₀ T, D = S ∪ T} := by
  classical
  have hT' : T ⊆ E ∧ c₀ ∈ T := by
    have ht := Finset.mem_filter.mp hT
    exact ⟨Finset.mem_powerset.mp ht.1, ht.2.1⟩
  have hfix : Φ.Tree E c₀ T = T := (lemma_3_2 Φ E c₀).2 T hT
  ext D
  constructor
  · rintro ⟨hDE, hcD, hDT⟩
    have hTD : T ⊆ D := by rw [← hDT]; exact run_subset_input Φ E D c₀ hcD
    have heq := sync_of_accepted Φ E D T c₀ E.card hTD (by change Φ.Tree E c₀ D ⊆ T; rw [hDT]) E.card le_rfl
    have hrejD := rejected_subset Φ E D c₀
    have hrej : ∀ c ∈ D, c ∉ Φ.rejected E c₀ T := by
      intro c hcD hcR
      apply (Finset.mem_sdiff.mp (hrejD ?_)).2 hcD
      change c ∈ ((Φ.treeStep E D)^[E.card] ({c₀}, ∅)).2
      rw [heq]
      exact hcR
    refine ⟨D \ T, ?_, ?_⟩
    · intro c hc
      have hd := Finset.mem_sdiff.mp hc
      simp only [CSP.free, Finset.mem_sdiff, Finset.mem_union, not_or]
      exact ⟨hDE hd.1, hd.2, hrej c hd.1⟩
    · ext c
      simp only [Finset.mem_union, Finset.mem_sdiff]
      constructor
      · intro hc
        by_cases hct : c ∈ T
        · exact Or.inr hct
        · exact Or.inl ⟨hc, hct⟩
      · rintro (⟨hd, _⟩ | ht)
        · exact hd
        · exact hTD ht
  · rintro ⟨S, hS, rfl⟩
    have hSE : S ⊆ E := by
      intro c hc
      exact (Finset.mem_sdiff.mp (hS hc)).1
    have hTA : T ⊆ S ∪ T := Finset.subset_union_right
    have havoid : ∀ c ∈ S ∪ T, c ∉ (Φ.treeRun E c₀ T).2 := by
      intro c hc
      rcases Finset.mem_union.mp hc with hs | ht
      · have hf := Finset.mem_sdiff.mp (hS hs)
        exact fun hr => hf.2 (Finset.mem_union.mpr (Or.inr hr))
      · have hr := rejected_subset Φ E T c₀
        exact fun hm => (Finset.mem_sdiff.mp (hr hm)).2 ht
    have heq := sync_of_rejected Φ E T (S ∪ T) c₀ E.card hTA havoid E.card le_rfl
    refine ⟨Finset.union_subset hSE hT'.1, Finset.mem_union.mpr (Or.inr hT'.2), ?_⟩
    change ((Φ.treeStep E (S ∪ T))^[E.card] ({c₀}, ∅)).1 = T
    rw [← heq]
    exact hfix

end CountingLLL.DetCount

open CountingLLL.DetCount
open CountingLLL.DetCount.CSP

theorem solution (Φ : CSP) (E : Finset (Fin Φ.m)) (c₀ : Fin Φ.m) (hc₀ : c₀ ∈ E)
    (T : Finset (Fin Φ.m)) (hT : T ∈ Φ.twoTrees E c₀) :
    {D : Finset (Fin Φ.m) | D ⊆ E ∧ c₀ ∈ D ∧ Φ.Tree E c₀ D = T} =
      {D : Finset (Fin Φ.m) | ∃ S ⊆ Φ.free E c₀ T, D = S ∪ T} := by
  exact inversion Φ E c₀ hc₀ T hT

