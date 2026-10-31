-- Prove2me | solution 1 for BudgetFeasSubmod.Main.definition_2_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T20:00:11.561286+00:00
-- url     : https://prove2.me/submissions/2d0a6ff2-31ec-406b-b192-33e4b46f4571

import Mathlib
import Definitions.Def_BudgetFeasSubmod_Main_Model

open BudgetFeasSubmod.Main Finset NonmonotoneSubmod.Shared

namespace BFS21

variable {A : Type} [Fintype A] [DecidableEq A]

lemma dim_of_sub (v : Finset A → ℝ) (hsub : Submodular v) (S T : Finset A) (i : A)
    (hST : S ⊆ T) (hi : i ∉ T) : marg v i T ≤ marg v i S := by
  unfold marg
  have h := hsub (insert i S) T
  have e1 : insert i S ∪ T = insert i T := by
    rw [Finset.insert_union, Finset.union_eq_right.mpr hST]
  have e2 : insert i S ∩ T = S := by
    rw [Finset.insert_inter_of_notMem hi, Finset.inter_eq_left.mpr hST]
  rw [e1, e2] at h
  linarith

lemma sub_of_dim (v : Finset A → ℝ)
    (h : ∀ S T : Finset A, ∀ i : A, S ⊆ T → i ∉ T → marg v i T ≤ marg v i S) : Submodular v := by
  intro S T
  -- adding the elements of Y ⊆ T \ S to S gains at most as much as adding them to S ∩ T
  have key : ∀ Y : Finset A, Y ⊆ T \ S → v (S ∪ Y) - v S ≤ v ((S ∩ T) ∪ Y) - v (S ∩ T) := by
    intro Y
    induction Y using Finset.induction_on with
    | empty => simp
    | insert a Y haY ih =>
      intro hY
      have haTS := hY (Finset.mem_insert_self a Y)
      have ih' := ih (le_trans (Finset.subset_insert a Y) hY)
      have haS : a ∉ S ∪ Y := by
        rw [Finset.mem_union]; rintro (h1 | h1)
        · exact (Finset.mem_sdiff.mp haTS).2 h1
        · exact haY h1
      have hsub : (S ∩ T) ∪ Y ⊆ S ∪ Y :=
        Finset.union_subset_union Finset.inter_subset_left (le_refl _)
      have hd := h _ _ a hsub haS
      unfold marg at hd
      rw [Finset.union_insert, Finset.union_insert]
      linarith
  have := key (T \ S) (le_refl _)
  have e1 : S ∪ (T \ S) = S ∪ T := Finset.union_sdiff_self_eq_union
  have e2 : (S ∩ T) ∪ (T \ S) = T := by
    ext a; simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]; tauto
  rw [e1, e2] at this
  linarith

lemma sum_marg (v : Finset A → ℝ) (hsub : Submodular v) (S T : Finset A) :
    v (S ∪ T) ≤ v S + ∑ a ∈ T, marg v a S := by
  induction T using Finset.induction_on with
  | empty => simp
  | insert a T haT ih =>
    rw [Finset.sum_insert haT]
    have h := hsub (insert a S) (S ∪ T)
    have e1 : insert a S ∪ (S ∪ T) = S ∪ insert a T := by
      ext y; simp only [Finset.mem_union, Finset.mem_insert]; tauto
    have e2 : insert a S ∩ (S ∪ T) = S := by
      ext y; simp only [Finset.mem_inter, Finset.mem_union, Finset.mem_insert]
      constructor
      · rintro ⟨rfl | h1, h2⟩
        · rcases h2 with h2 | h2
          · exact h2
          · exact absurd h2 haT
        · exact h1
      · intro h; exact ⟨Or.inr h, Or.inl h⟩
    rw [e1, e2] at h
    unfold marg at ih ⊢
    linarith

lemma remove_marg (v : Finset A → ℝ) (hsub : Submodular v) (W T : Finset A) :
    ∀ Z : Finset A, Z ⊆ W → T ⊆ W → Disjoint Z T →
      ∑ a ∈ Z, marg v a (W.erase a) ≤ v (T ∪ Z) - v T := by
  intro Z
  induction Z using Finset.induction_on with
  | empty => intros; simp
  | insert a Z haZ ih =>
    intro hZW hTW hdisj
    rw [Finset.sum_insert haZ]
    have ih' := ih (le_trans (Finset.subset_insert _ _) hZW) hTW
      (Finset.disjoint_of_subset_left (Finset.subset_insert _ _) hdisj)
    have haT : a ∉ T := Finset.disjoint_left.mp hdisj (Finset.mem_insert_self _ _)
    have haTZ : a ∉ T ∪ Z := by
      rw [Finset.mem_union]; rintro (h | h); exact haT h; exact haZ h
    have hsubset : T ∪ Z ⊆ W.erase a := by
      intro y hy
      refine Finset.mem_erase.mpr ⟨fun e => haTZ (e ▸ hy), ?_⟩
      rcases Finset.mem_union.mp hy with h | h
      · exact hTW h
      · exact hZW (Finset.mem_insert_of_mem h)
    have hd := dim_of_sub v hsub _ _ a hsubset (Finset.notMem_erase a W)
    unfold marg at hd ih' ⊢
    rw [Finset.union_insert]
    linarith

end BFS21

open BFS21 in
theorem solution {A : Type} [Fintype A] [DecidableEq A] (v : Finset A → ℝ) :
    (Submodular v ↔
      ∀ S T : Finset A, ∀ i : A, S ⊆ T → i ∉ T → marg v i T ≤ marg v i S) ∧
    (Submodular v ↔
      ∀ S T : Finset A,
        v T ≤ v S + ∑ i ∈ T \ S, marg v i S - ∑ i ∈ S \ T, marg v i ((S ∪ T).erase i)) := by
  refine ⟨⟨fun h S T i hST hi => dim_of_sub v h S T i hST hi, sub_of_dim v⟩, ⟨?_, ?_⟩⟩
  · intro h S T
    have h1 := sum_marg v h S (T \ S)
    rw [Finset.union_sdiff_self_eq_union] at h1
    have h2 := remove_marg v h (S ∪ T) T (S \ T) (Finset.sdiff_subset.trans Finset.subset_union_left)
      Finset.subset_union_right Finset.sdiff_disjoint
    have e : T ∪ (S \ T) = S ∪ T := by
      rw [Finset.union_sdiff_self_eq_union, Finset.union_comm]
    rw [e] at h2
    linarith
  · intro h
    apply sub_of_dim
    -- diminishing returns from the two-element case
    have pair : ∀ (S : Finset A) (i j : A), i ∉ S → j ∉ S → i ≠ j →
        marg v i (insert j S) ≤ marg v i S := by
      intro S i j hi hj hij
      have h0 := h (insert i (insert j S)) S
      have d1 : S \ insert i (insert j S) = ∅ := by
        ext a; simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.notMem_empty, iff_false]
        tauto
      have d2 : insert i (insert j S) \ S = {i, j} := by
        ext a; simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro ⟨h1 | h1 | h1, h2⟩
          · exact Or.inl h1
          · exact Or.inr h1
          · exact absurd h1 h2
        · rintro (rfl | rfl)
          · exact ⟨Or.inl rfl, hi⟩
          · exact ⟨Or.inr (Or.inl rfl), hj⟩
      have hu : insert i (insert j S) ∪ S = insert i (insert j S) := by
        rw [Finset.union_eq_left]; intro a ha
        exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem ha)
      rw [d1, d2, hu, Finset.sum_empty, Finset.sum_pair hij] at h0
      have er1 : (insert i (insert j S)).erase i = insert j S := by
        rw [Finset.erase_insert]
        rw [Finset.mem_insert]; rintro (h1 | h1); exact hij h1; exact hi h1
      have er2 : (insert i (insert j S)).erase j = insert i S := by
        rw [Finset.insert_comm, Finset.erase_insert]
        rw [Finset.mem_insert]; rintro (h1 | h1); exact hij h1.symm; exact hj h1
      rw [er1, er2] at h0
      unfold marg at h0 ⊢
      rw [Finset.insert_comm i j S] at h0 ⊢
      linarith
    intro S T i hST hiT
    have key : ∀ Z : Finset A, Disjoint Z S → i ∉ Z → i ∉ S →
        marg v i (S ∪ Z) ≤ marg v i S := by
      intro Z
      induction Z using Finset.induction_on with
      | empty => intros; simp
      | insert a Z haZ ih =>
        intro hd hiZ hiS
        have hiZ' : i ∉ Z := fun h' => hiZ (Finset.mem_insert_of_mem h')
        have ih' := ih (Finset.disjoint_of_subset_left (Finset.subset_insert _ _) hd) hiZ' hiS
        have haSZ : a ∉ S ∪ Z := by
          rw [Finset.mem_union]; rintro (h1 | h1)
          · exact Finset.disjoint_left.mp hd (Finset.mem_insert_self _ _) h1
          · exact haZ h1
        have hiSZ : i ∉ S ∪ Z := by
          rw [Finset.mem_union]; rintro (h1 | h1); exact hiS h1; exact hiZ' h1
        have hia : i ≠ a := fun e => hiZ (e ▸ Finset.mem_insert_self _ _)
        have := pair (S ∪ Z) i a hiSZ haSZ hia
        rw [Finset.union_insert]
        linarith
    have := key (T \ S) Finset.sdiff_disjoint (fun h' => hiT (Finset.mem_sdiff.mp h').1)
      (fun h' => hiT (hST h'))
    rw [Finset.union_sdiff_of_subset hST] at this
    exact this
