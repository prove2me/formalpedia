-- Prove2me | solution 1 for Conway99.ten_of_no_four_diag_count
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-08T00:24:12.618905+00:00
-- url     : https://prove2.me/submissions/af9d2c0e-527c-4e9a-b10c-bd475f243392

import Mathlib

open scoped BigOperators

theorem solution
    (C : Matrix (Fin 9) (Fin 9) ℕ)
    (hdiag : ∀ i, C i i = 0 ∨ C i i = 2 ∨ C i i = 4)
    (htr : ∑ i, C i i = 10)
    (hfour : ∀ i, C i i ≠ 4) :
    (Finset.univ.filter (fun i => C i i = 2)).card = 5 ∧
    (Finset.univ.filter (fun i => C i i = 0)).card = 4 := by
  have h02 : ∀ i ∈ Finset.univ, C i i = 0 ∨ C i i = 2 := by
    intro i _
    rcases hdiag i with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact absurd h (hfour i)
  have h2sum : ∑ i ∈ Finset.univ.filter (fun i => C i i = 2), C i i =
      2 * (Finset.univ.filter (fun i => C i i = 2)).card := by
    have hc := Finset.sum_eq_card_nsmul (s := Finset.univ.filter (fun i => C i i = 2))
      (f := fun i => C i i) (b := 2)
      (fun i hi => (Finset.mem_filter.mp hi).2)
    simpa [nsmul_eq_mul, Nat.mul_comm] using hc
  have h0sum : ∑ i ∈ Finset.univ.filter (fun i => C i i = 0), C i i = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    exact (Finset.mem_filter.mp hi).2
  have hunion : Finset.univ.filter (fun i => C i i = 2) ∪ Finset.univ.filter (fun i => C i i = 0) =
      Finset.univ := by
    ext i
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun _ => trivial, fun _ => (h02 i (Finset.mem_univ i)).symm⟩
  have hdisj : Disjoint (Finset.univ.filter (fun i => C i i = 2))
      (Finset.univ.filter (fun i => C i i = 0)) := by
    rw [Finset.disjoint_left]
    intro i hi hcon
    rw [Finset.mem_filter] at hcon
    have h2 := (Finset.mem_filter.mp hi).2
    omega
  have hsplit : (∑ i ∈ Finset.univ.filter (fun i => C i i = 2), C i i) +
      (∑ i ∈ Finset.univ.filter (fun i => C i i = 0), C i i) = 10 := by
    have hU : (∑ i ∈ Finset.univ.filter (fun i => C i i = 2) ∪
        Finset.univ.filter (fun i => C i i = 0), C i i) =
        (∑ i ∈ Finset.univ.filter (fun i => C i i = 2), C i i) +
        (∑ i ∈ Finset.univ.filter (fun i => C i i = 0), C i i) :=
      Finset.sum_union hdisj
    rw [hunion] at hU
    calc (∑ i ∈ Finset.univ.filter (fun i => C i i = 2), C i i) +
            (∑ i ∈ Finset.univ.filter (fun i => C i i = 0), C i i)
        = ∑ x, C x x := hU.symm
      _ = 10 := htr
  rw [h2sum, h0sum] at hsplit
  have hcard : (Finset.univ.filter (fun i => C i i = 2)).card +
      (Finset.univ.filter (fun i => C i i = 0)).card = 9 := by
    have h := Finset.card_union_of_disjoint hdisj
    rw [hunion] at h
    have h9 : (Finset.univ : Finset (Fin 9)).card = 9 := by simp [Finset.card_univ]
    omega
  omega

