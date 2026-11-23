-- Prove2me | solution 1 for BeyondGomoryHu.Units.lemma_2_6
-- status  : ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T02:43:15.864239+00:00
-- url     : https://prove2.me/submissions/32a0c4ee-dacd-486a-a26c-048e839e8d99

import Mathlib
import Definitions.Def_BeyondGomoryHu_Units_Hierarchy

set_option autoImplicit false
set_option maxHeartbeats 1000000

open BeyondGomoryHu.Units

private lemma cap_eq_sum_univ {V : Type} [Fintype V] [DecidableEq V]
    (G : WGraph V) (X : Finset V) :
    cap G X = ∑ a : V, ∑ b : V, if a ∈ X ∧ b ∉ X then G.w a b else 0 := by
  simp [cap, ite_and, Finset.sum_ite]
  apply Finset.sum_congr rfl
  intro a ha
  congr 1
  ext b
  simp

private lemma cap_fourComponents_ineq {V : Type} [Fintype V] [DecidableEq V]
    (G : WGraph V) (A B C : Finset V) :
    cap G (A \ (B ∪ C)) + cap G (B \ (A ∪ C)) +
        cap G (C \ (A ∪ B)) + cap G (A ∩ B ∩ C) ≤
      cap G A + cap G B + cap G C := by
  let cross : Finset V → V → V → ℕ := fun X a b =>
    if a ∈ X ∧ b ∉ X then G.w a b else 0
  let pcap : Finset V → ℕ := fun X => ∑ a : V, ∑ b : V, (cross X a b + cross X b a)
  have hdouble (X : Finset V) : pcap X = cap G X + cap G X := by
    have hrev : (∑ a : V, ∑ b : V, cross X b a) = ∑ a : V, ∑ b : V, cross X a b := by
      exact Finset.sum_comm
    dsimp [pcap]
    simp only [Finset.sum_add_distrib]
    rw [hrev]
    simp only [cross, ← cap_eq_sum_univ]
  have hpoint (a b : V) :
      ((cross (A \ (B ∪ C)) a b + cross (A \ (B ∪ C)) b a) +
        (cross (B \ (A ∪ C)) a b + cross (B \ (A ∪ C)) b a) +
        (cross (C \ (A ∪ B)) a b + cross (C \ (A ∪ B)) b a) +
        (cross (A ∩ B ∩ C) a b + cross (A ∩ B ∩ C) b a)) ≤
      ((cross A a b + cross A b a) + (cross B a b + cross B b a) +
        (cross C a b + cross C b a)) := by
    by_cases haA : a ∈ A <;> by_cases haB : a ∈ B <;> by_cases haC : a ∈ C <;>
      by_cases hbA : b ∈ A <;> by_cases hbB : b ∈ B <;> by_cases hbC : b ∈ C <;>
      simp [cross, haA, haB, haC, hbA, hbB, hbC, G.symm]
  have htwo :
      (cap G (A \ (B ∪ C)) + cap G (A \ (B ∪ C))) +
        (cap G (B \ (A ∪ C)) + cap G (B \ (A ∪ C))) +
        (cap G (C \ (A ∪ B)) + cap G (C \ (A ∪ B))) +
        (cap G (A ∩ B ∩ C) + cap G (A ∩ B ∩ C)) ≤
      (cap G A + cap G A) + (cap G B + cap G B) + (cap G C + cap G C) := by
    rw [← hdouble, ← hdouble, ← hdouble, ← hdouble, ← hdouble, ← hdouble, ← hdouble]
    calc
      pcap (A \ (B ∪ C)) + pcap (B \ (A ∪ C)) + pcap (C \ (A ∪ B)) +
          pcap (A ∩ B ∩ C) =
          ∑ a : V, ∑ b : V,
            ((cross (A \ (B ∪ C)) a b + cross (A \ (B ∪ C)) b a) +
              (cross (B \ (A ∪ C)) a b + cross (B \ (A ∪ C)) b a) +
              (cross (C \ (A ∪ B)) a b + cross (C \ (A ∪ B)) b a) +
              (cross (A ∩ B ∩ C) a b + cross (A ∩ B ∩ C) b a)) := by
        simp only [pcap, Finset.sum_add_distrib]
      _ ≤ ∑ a : V, ∑ b : V,
            ((cross A a b + cross A b a) + (cross B a b + cross B b a) +
              (cross C a b + cross C b a)) := by
        exact Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => hpoint a b
      _ = pcap A + pcap B + pcap C := by
        simp only [pcap, Finset.sum_add_distrib]
  omega

private lemma eq_empty_or_univ_of_cap_eq_zero {V : Type} [Fintype V] [DecidableEq V]
    (G : WGraph V) (hG : G.Connected) (X : Finset V) (hX : cap G X = 0) :
    X = ∅ ∨ X = Finset.univ := by
  have hw_zero (a : V) (ha : a ∈ X) (b : V) (hb : b ∈ Xᶜ) : G.w a b = 0 := by
    apply Nat.eq_zero_of_le_zero
    calc
      G.w a b ≤ ∑ b' ∈ Xᶜ, G.w a b' :=
        Finset.single_le_sum (fun _ _ => Nat.zero_le _) hb
      _ ≤ ∑ a' ∈ X, ∑ b' ∈ Xᶜ, G.w a' b' :=
        Finset.single_le_sum
          (fun a' _ => Finset.sum_nonneg (fun b' _ => Nat.zero_le (G.w a' b'))) ha
      _ = 0 := hX
  let H := SimpleGraph.fromRel (fun a b => 0 < G.w a b)
  have no_cross {a b : V} (hab : H.Adj a b) : (a ∈ X ↔ b ∈ X) := by
    have hw : 0 < G.w a b := by
      rcases ((SimpleGraph.fromRel_adj _ _ _).mp hab).2 with h | h
      · exact h
      · rwa [G.symm b a] at h
    by_cases ha : a ∈ X <;> by_cases hb : b ∈ X
    · simp [ha, hb]
    · have hb' : b ∈ Xᶜ := Finset.mem_compl.mpr hb
      have := hw_zero a ha b hb'
      omega
    · have ha' : a ∈ Xᶜ := Finset.mem_compl.mpr ha
      have hz := hw_zero b hb a ha'
      rw [G.symm] at hz
      omega
    · simp [ha, hb]
  have mem_iff_of_reachable {a b : V} (hab : H.Reachable a b) : (a ∈ X ↔ b ∈ X) := by
    obtain ⟨p⟩ := hab
    induction p with
    | nil => rfl
    | cons huv p ih => exact (no_cross huv).trans ih
  rcases Finset.eq_empty_or_nonempty X with h | h
  · exact Or.inl h
  · right
    obtain ⟨a, ha⟩ := h
    apply Finset.eq_univ_iff_forall.mpr
    intro b
    by_contra hb
    have hab : H.Reachable a b := hG.preconnected a b
    exact hb ((mem_iff_of_reachable hab).mp ha)

private lemma fourComponents_disjoint {V : Type} [DecidableEq V]
    (A B C : Finset V) {i j : Fin 4} (hij : i ≠ j) :
    Disjoint (fourComponents A B C i) (fourComponents A B C j) := by
  fin_cases i <;> fin_cases j <;> simp_all [fourComponents, Finset.disjoint_left]

theorem solution {V : Type} [Fintype V] [DecidableEq V] (G : WGraph V) (hG : G.Connected) (S T W A B C : Finset V)
    (hA : IsMincut G S A) (hB : IsMincut G T B) (hC : IsMincut G W C)
    (i j l m : Fin 4) (hij : i ≠ j) (hil : i ≠ l) (him : i ≠ m) (hjl : j ≠ l) (hjm : j ≠ m)
    (hlm : l ≠ m) (hi : IsCut S (fourComponents A B C i)) (hj : IsCut T (fourComponents A B C j))
    (hl : IsCut W (fourComponents A B C l)) :
    fourComponents A B C m = ∅ := by
  have hAi := hA.2 _ hi
  have hBj := hB.2 _ hj
  have hCl := hC.2 _ hl
  have hcap := cap_fourComponents_ineq G A B C
  have hsum : cap G (A \ (B ∪ C)) + cap G (B \ (A ∪ C)) +
        cap G (C \ (A ∪ B)) + cap G (A ∩ B ∩ C) =
      cap G (fourComponents A B C i) + cap G (fourComponents A B C j) +
        cap G (fourComponents A B C l) + cap G (fourComponents A B C m) := by
    fin_cases i <;> fin_cases j <;> fin_cases l <;> fin_cases m <;>
      simp_all [fourComponents] <;> omega
  have hzero : cap G (fourComponents A B C m) = 0 := by
    rw [hsum] at hcap
    omega
  rcases eq_empty_or_univ_of_cap_eq_zero G hG _ hzero with h | h
  · exact h
  · have hne : (fourComponents A B C i).Nonempty :=
      hi.1.mono Finset.inter_subset_left
    obtain ⟨x, hx⟩ := hne
    have hxm : x ∉ fourComponents A B C m :=
      Finset.disjoint_left.mp (fourComponents_disjoint A B C him) hx
    exact (hxm (by simp [h])).elim
