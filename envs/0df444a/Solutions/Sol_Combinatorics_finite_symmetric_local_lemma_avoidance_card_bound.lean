-- Prove2me | solution 1 for Combinatorics.finite_symmetric_local_lemma_avoidance_card_bound
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T02:52:45.969693+00:00
-- url     : https://prove2.me/submissions/df657a84-0d28-44be-b847-6438b8f889c8

import Mathlib

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace LLLAux

variable {Omega I : Type*} [Fintype Omega] [DecidableEq Omega] [Fintype I] [DecidableEq I]

def G (A : I → Finset Omega) (S : Finset I) : Finset Omega :=
  Finset.univ.filter (fun w => ∀ j, Membership.mem S j → Not (Membership.mem (A j) w))

lemma G_insert (A : I → Finset Omega) (j : I) (S : Finset I) :
    G A (insert j S) = (G A S).filter (fun w => ¬ w ∈ A j) := by
  ext w
  simp only [G, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
  constructor
  · intro h
    exact ⟨fun k hk => h k (Or.inr hk), h j (Or.inl rfl)⟩
  · rintro ⟨h1, h2⟩ k hk
    rcases hk with rfl | hk
    · exact h2
    · exact h1 k hk

lemma card_G_insert (A : I → Finset Omega) (j : I) (S : Finset I) :
    ((G A (insert j S)).card : ℝ) =
      (G A S).card - ((G A S).filter (fun w => w ∈ A j)).card := by
  rw [G_insert]
  have := Finset.card_filter_add_card_filter_not (s := G A S) (fun w => w ∈ A j)
  rw [← this]; push_cast; ring

lemma G_mono (A : I → Finset Omega) {S T : Finset I} (h : S ⊆ T) : G A T ⊆ G A S := by
  intro w
  simp only [G, Finset.mem_filter, Finset.mem_univ, true_and]
  intro hw j hj
  exact hw j (h hj)

theorem claim [Nonempty Omega] (A : I → Finset Omega) (dep : I → I → Prop)
    [DecidableRel dep] (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x < 1)
    (hprob : ∀ i, ((A i).card : ℝ) / (Fintype.card Omega : ℝ) ≤
      x * (1 - x) ^ (Finset.univ.filter (fun j => dep i j)).card)
    (hind : ∀ (i : I) (S : Finset I), (∀ j, j ∈ S → ¬ dep i j) →
      (((G A S).filter (fun w => w ∈ A i)).card : ℝ) / (Fintype.card Omega : ℝ) =
        (((G A S).card : ℝ) / (Fintype.card Omega : ℝ)) * ((A i).card : ℝ) /
          (Fintype.card Omega : ℝ)) :
    ∀ (n : ℕ) (S : Finset I), S.card = n → ∀ i,
      (((G A S).filter (fun w => w ∈ A i)).card : ℝ) ≤ x * (G A S).card := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro S hS i
  set S2 := S.filter (fun j => ¬ dep i j) with hS2
  set S1 := S.filter (fun j => dep i j) with hS1
  have hN : (0:ℝ) < Fintype.card Omega := by exact_mod_cast Fintype.card_pos
  have h1x : 0 ≤ 1 - x := by linarith
  have h1 : (((G A S).filter (fun w => w ∈ A i)).card : ℝ) ≤
      ((G A S2).filter (fun w => w ∈ A i)).card := by
    exact_mod_cast Finset.card_le_card
      (Finset.filter_subset_filter _ (G_mono A (Finset.filter_subset _ _)))
  have h2 : (((G A S2).filter (fun w => w ∈ A i)).card : ℝ) ≤
      x * (1 - x) ^ (Finset.univ.filter (fun j => dep i j)).card * (G A S2).card := by
    have e := hind i S2 (fun j hj => (Finset.mem_filter.mp hj).2)
    have hp := hprob i
    rw [div_le_iff₀ hN] at hp
    have e' : (((G A S2).filter (fun w => w ∈ A i)).card : ℝ) =
        (G A S2).card * (A i).card / Fintype.card Omega := by
      have hNne : (Fintype.card Omega : ℝ) ≠ 0 := ne_of_gt hN
      field_simp at e
      field_simp
      linarith
    rw [e', div_le_iff₀ hN]
    have hG : (0:ℝ) ≤ (G A S2).card := by positivity
    calc ((G A S2).card : ℝ) * (A i).card
        ≤ (G A S2).card * (x * (1 - x) ^ (Finset.univ.filter (fun j => dep i j)).card *
            Fintype.card Omega) := mul_le_mul_of_nonneg_left hp hG
      _ = _ := by ring
  have h3 : ∀ T : Finset I, T ⊆ S1 →
      (1 - x) ^ T.card * ((G A S2).card : ℝ) ≤ (G A (S2 ∪ T)).card := by
    intro T
    induction T using Finset.induction_on with
    | empty => intro _; simp
    | insert j T hjT ihT =>
      intro hsub
      have hjS1 : j ∈ S1 := hsub (Finset.mem_insert_self _ _)
      have hT : T ⊆ S1 := fun t ht => hsub (Finset.mem_insert_of_mem ht)
      have hprev := ihT hT
      have hU : S2 ∪ insert j T = insert j (S2 ∪ T) := by
        ext k; simp only [Finset.mem_union, Finset.mem_insert]; tauto
      rw [hU, card_G_insert, Finset.card_insert_of_notMem hjT, pow_succ]
      have hlt : (S2 ∪ T).card < n := by
        rw [← hS]
        apply Finset.card_lt_card
        refine ⟨?_, ?_⟩
        · exact Finset.union_subset (Finset.filter_subset _ _)
            (hT.trans (Finset.filter_subset _ _))
        · intro hsub2
          have hjS : j ∈ S := (Finset.mem_filter.mp hjS1).1
          rcases Finset.mem_union.mp (hsub2 hjS) with h | h
          · exact (Finset.mem_filter.mp h).2 (Finset.mem_filter.mp hjS1).2
          · exact hjT h
      have hb := ih _ hlt (S2 ∪ T) rfl j
      have hm := mul_le_mul_of_nonneg_left hprev h1x
      nlinarith
  have hS12 : S2 ∪ S1 = S := by
    ext k; simp only [hS1, hS2, Finset.mem_union, Finset.mem_filter]; tauto
  have h4 := h3 S1 le_rfl
  rw [hS12] at h4
  have h5 : (1 - x) ^ (Finset.univ.filter (fun j => dep i j)).card ≤ (1 - x) ^ S1.card := by
    apply pow_le_pow_of_le_one h1x (by linarith)
    apply Finset.card_le_card
    intro k hk
    simp only [hS1, Finset.mem_filter] at hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hk.2
  have hG : (0:ℝ) ≤ (G A S2).card := by positivity
  calc (((G A S).filter (fun w => w ∈ A i)).card : ℝ)
      ≤ x * (1 - x) ^ (Finset.univ.filter (fun j => dep i j)).card * (G A S2).card := h1.trans h2
    _ ≤ x * ((1 - x) ^ S1.card * (G A S2).card) := by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h5 hG) hx0
    _ ≤ x * (G A S).card := mul_le_mul_of_nonneg_left h4 hx0

end LLLAux

open Combinatorics in
theorem solution
    (Omega I : Type*) [Fintype Omega] [Nonempty Omega] [DecidableEq Omega]
    [Fintype I] [DecidableEq I]
    (A : I -> Finset Omega) (dep : I -> I -> Prop) [DecidableRel dep]
    (x : Real) (hx0 : 0 <= x) (hx1 : x < 1)
    (hprob : forall i,
      ((A i).card : Real) / (Fintype.card Omega : Real) <=
        x * (1 - x) ^ (Finset.univ.filter (fun j => dep i j)).card)
    (hindependent : forall (i : I) (S : Finset I),
      (forall j, Membership.mem S j -> Not (dep i j)) ->
      ((Finset.filter (fun w => Membership.mem (A i) w)
          (Finset.univ.filter (fun w => forall j, Membership.mem S j ->
            Not (Membership.mem (A j) w)))).card : Real) /
          (Fintype.card Omega : Real) =
        (((Finset.univ.filter (fun w => forall j, Membership.mem S j ->
            Not (Membership.mem (A j) w))).card : Real) /
            (Fintype.card Omega : Real)) *
          ((A i).card : Real) / (Fintype.card Omega : Real)) :
    forall S : Finset I,
      (1 - x) ^ S.card * (Fintype.card Omega : Real) <=
        ((Finset.univ.filter (fun w : Omega =>
          forall j, Membership.mem S j -> Not (Membership.mem (A j) w))).card : Real) := by
  have hc := LLLAux.claim A dep x hx0 hx1 hprob (fun i S h => hindependent i S h)
  have h1x : 0 ≤ 1 - x := by linarith
  intro S
  induction S using Finset.induction_on with
  | empty => simp
  | insert j S hjS ihS =>
    change _ ≤ ((LLLAux.G A (insert j S)).card : ℝ)
    change (1 - x) ^ S.card * _ ≤ ((LLLAux.G A S).card : ℝ) at ihS
    rw [LLLAux.card_G_insert, Finset.card_insert_of_notMem hjS, pow_succ]
    have hb := hc _ S rfl j
    have hm := mul_le_mul_of_nonneg_left ihS h1x
    nlinarith
