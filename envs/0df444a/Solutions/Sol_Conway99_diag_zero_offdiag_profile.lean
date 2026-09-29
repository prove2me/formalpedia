-- Prove2me | solution 1 for Conway99.diag_zero_offdiag_profile
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-08T00:08:33.767865+00:00
-- url     : https://prove2.me/submissions/37f1f6e5-dd93-4bab-8b2c-1da88852480d

import Mathlib

open scoped BigOperators

theorem solution
    (C : Matrix (Fin 9) (Fin 9) ℕ) (hsymm : ∀ i j, C i j = C j i)
    (hrow : ∀ i, ∑ j, C i j = 14)
    (hsq : ∀ i j, (∑ k, C i k * C k j) + C i j = (if i = j then 12 else 0) + 22)
    (i : Fin 9) (hi : C i i = 0) :
    ((((Finset.univ.erase i).filter (fun k => C i k = 0)).card = 2 ∧
      ((Finset.univ.erase i).filter (fun k => C i k = 1)).card = 0 ∧
      ((Finset.univ.erase i).filter (fun k => C i k = 2)).card = 4 ∧
      ((Finset.univ.erase i).filter (fun k => C i k = 3)).card = 2 ∧
      ((Finset.univ.erase i).filter (fun k => C i k = 4)).card = 0 ∧
      ((Finset.univ.erase i).filter (fun k => C i k = 5)).card = 0) ∨
     (((Finset.univ.erase i).filter (fun k => C i k = 0)).card = 1 ∧
      ((Finset.univ.erase i).filter (fun k => C i k = 1)).card = 3 ∧
      ((Finset.univ.erase i).filter (fun k => C i k = 2)).card = 1 ∧
      ((Finset.univ.erase i).filter (fun k => C i k = 3)).card = 3 ∧
      ((Finset.univ.erase i).filter (fun k => C i k = 4)).card = 0 ∧
      ((Finset.univ.erase i).filter (fun k => C i k = 5)).card = 0) ∨
     (((Finset.univ.erase i).filter (fun k => C i k = 0)).card = 1 ∧
      ((Finset.univ.erase i).filter (fun k => C i k = 1)).card = 2 ∧
      ((Finset.univ.erase i).filter (fun k => C i k = 2)).card = 4 ∧
      ((Finset.univ.erase i).filter (fun k => C i k = 3)).card = 0 ∧
      ((Finset.univ.erase i).filter (fun k => C i k = 4)).card = 1 ∧
      ((Finset.univ.erase i).filter (fun k => C i k = 5)).card = 0) ∨
     (((Finset.univ.erase i).filter (fun k => C i k = 0)).card = 0 ∧
      ((Finset.univ.erase i).filter (fun k => C i k = 1)).card = 5 ∧
      ((Finset.univ.erase i).filter (fun k => C i k = 2)).card = 1 ∧
      ((Finset.univ.erase i).filter (fun k => C i k = 3)).card = 1 ∧
      ((Finset.univ.erase i).filter (fun k => C i k = 4)).card = 1 ∧
      ((Finset.univ.erase i).filter (fun k => C i k = 5)).card = 0)) := by
  have hsqsum : ∑ k, C i k ^ 2 = 34 := by
    have h := hsq i i
    rw [if_pos rfl] at h
    have hsum : (∑ k, C i k * C k i) = ∑ k, C i k ^ 2 := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [← hsymm i k, pow_two]
    rw [hsum, hi] at h
    omega
  have hsum_off : Finset.sum (Finset.univ.erase i) (fun k => C i k) = 14 := by
    have h := hrow i
    have hsplit := Finset.sum_erase_add (Finset.univ : Finset (Fin 9)) (fun k => C i k) (Finset.mem_univ i)
    rw [hi] at hsplit
    omega
  have hsq_off : Finset.sum (Finset.univ.erase i) (fun k => C i k ^ 2) = 34 := by
    have hsplit := Finset.sum_erase_add (Finset.univ : Finset (Fin 9)) (fun k => C i k ^ 2) (Finset.mem_univ i)
    have hii_sq : C i i ^ 2 = 0 := by simp [hi]
    omega
  have hbound : ∀ k ∈ Finset.univ.erase i, C i k ≤ 5 := by
    intro k hk
    by_contra hgt
    push Not at hgt
    have h6 : 6 ≤ C i k := hgt
    have h36 : 36 ≤ C i k ^ 2 := by
      have hmul := Nat.mul_le_mul h6 h6
      calc (36 : ℕ) = 6 * 6 := by omega
        _ ≤ C i k * C i k := hmul
        _ = C i k ^ 2 := by rw [pow_two]
    have hle : C i k ^ 2 ≤ Finset.sum (Finset.univ.erase i) (fun k => C i k ^ 2) :=
      Finset.single_le_sum (f := fun k => C i k ^ 2) (fun k hk => Nat.zero_le _) hk
    omega
  let S := Finset.univ.erase i
  let T := Finset.range 6
  let v : Fin 9 → ℕ := fun k => C i k
  have hmap : ∀ k ∈ S, v k ∈ T := by
    intro k hk
    simp [T, v]
    have hb := hbound k hk
    dsimp [S] at hk
    omega
  have htotal : ∑ j ∈ T, (S.filter (fun k => v k = j)).card = 8 := by
    have hf := Finset.sum_fiberwise_of_maps_to (s := S) (t := T) hmap (fun _ => 1)
    have hfib : ∀ j ∈ T, (∑ k ∈ S with v k = j, (1 : ℕ)) = (S.filter (fun k => v k = j)).card := by
      intro j hj
      rw [Finset.sum_const, nsmul_eq_mul, mul_one]
      rfl
    have hsum : ∑ j ∈ T, (S.filter (fun k => v k = j)).card = 8 := by
      calc
        ∑ j ∈ T, (S.filter (fun k => v k = j)).card =
            ∑ j ∈ T, ∑ k ∈ S with v k = j, (1 : ℕ) := by
              apply Finset.sum_congr rfl
              intro j hj
              rw [hfib j hj]
        _ = ∑ k ∈ S, (1 : ℕ) := hf
        _ = 8 := by simp [S]
    exact hsum
  have hweighted : ∑ j ∈ T, j * (S.filter (fun k => v k = j)).card = 14 := by
    have hf := Finset.sum_fiberwise_of_maps_to (s := S) (t := T) hmap (fun k => v k)
    have hfib : ∀ j ∈ T, (∑ k ∈ S with v k = j, v k) = j * (S.filter (fun k => v k = j)).card := by
      intro j hj
      have hc := Finset.sum_eq_card_nsmul (s := S.filter (fun k => v k = j))
        (f := fun k => v k) (b := j)
        (fun k hk => by simp [(Finset.mem_filter.mp hk).2])
      simpa [nsmul_eq_mul, Nat.mul_comm] using hc
    have hsum : ∑ j ∈ T, j * (S.filter (fun k => v k = j)).card = 14 := by
      calc
        ∑ j ∈ T, j * (S.filter (fun k => v k = j)).card =
            ∑ j ∈ T, ∑ k ∈ S with v k = j, v k := by
              apply Finset.sum_congr rfl
              intro j hj
              rw [hfib j hj]
        _ = ∑ k ∈ S, v k := hf
        _ = 14 := hsum_off
    exact hsum
  have hweighted_sq : ∑ j ∈ T, j ^ 2 * (S.filter (fun k => v k = j)).card = 34 := by
    have hf := Finset.sum_fiberwise_of_maps_to (s := S) (t := T) hmap (fun k => v k ^ 2)
    have hfib : ∀ j ∈ T, (∑ k ∈ S with v k = j, v k ^ 2) = j ^ 2 * (S.filter (fun k => v k = j)).card := by
      intro j hj
      have hc := Finset.sum_eq_card_nsmul (s := S.filter (fun k => v k = j))
        (f := fun k => v k ^ 2) (b := j ^ 2)
        (fun k hk => by simp [(Finset.mem_filter.mp hk).2])
      simpa [nsmul_eq_mul, Nat.mul_comm] using hc
    have hsum : ∑ j ∈ T, j ^ 2 * (S.filter (fun k => v k = j)).card = 34 := by
      calc
        ∑ j ∈ T, j ^ 2 * (S.filter (fun k => v k = j)).card =
            ∑ j ∈ T, ∑ k ∈ S with v k = j, v k ^ 2 := by
              apply Finset.sum_congr rfl
              intro j hj
              rw [hfib j hj]
        _ = ∑ k ∈ S, v k ^ 2 := hf
        _ = 34 := hsq_off
    exact hsum
  have e0 : (S.filter (fun k => v k = 0)).card + (S.filter (fun k => v k = 1)).card +
      (S.filter (fun k => v k = 2)).card + (S.filter (fun k => v k = 3)).card +
      (S.filter (fun k => v k = 4)).card + (S.filter (fun k => v k = 5)).card = 8 := by
    simpa [T, Finset.sum_range_succ] using htotal
  have e1 : (S.filter (fun k => v k = 1)).card + 2 * (S.filter (fun k => v k = 2)).card +
      3 * (S.filter (fun k => v k = 3)).card + 4 * (S.filter (fun k => v k = 4)).card +
      5 * (S.filter (fun k => v k = 5)).card = 14 := by
    simpa [T, Finset.sum_range_succ, Nat.add_assoc, Nat.mul_comm, Nat.mul_left_comm,
      Nat.mul_assoc] using hweighted
  have e2 : (S.filter (fun k => v k = 1)).card + 4 * (S.filter (fun k => v k = 2)).card +
      9 * (S.filter (fun k => v k = 3)).card + 16 * (S.filter (fun k => v k = 4)).card +
      25 * (S.filter (fun k => v k = 5)).card = 34 := by
    simpa [T, Finset.sum_range_succ, Nat.add_assoc, Nat.mul_comm, Nat.mul_left_comm,
      Nat.mul_assoc] using hweighted_sq
  have w : (S.filter (fun k => v k = 0)).card + (S.filter (fun k => v k = 3)).card +
      3 * (S.filter (fun k => v k = 4)).card +
      6 * (S.filter (fun k => v k = 5)).card = 4 := by
    omega
  have c5z : (S.filter (fun k => v k = 5)).card = 0 := by omega
  have c4split : (S.filter (fun k => v k = 4)).card = 0 ∨
      (S.filter (fun k => v k = 4)).card = 1 := by omega
  rcases c4split with h4 | h4
  · have c3split : (S.filter (fun k => v k = 3)).card = 2 ∨
        (S.filter (fun k => v k = 3)).card = 3 := by omega
    rcases c3split with h3 | h3
    · have g0 : (S.filter (fun k => v k = 0)).card = 2 := by omega
      have g1 : (S.filter (fun k => v k = 1)).card = 0 := by omega
      have g2 : (S.filter (fun k => v k = 2)).card = 4 := by omega
      exact Or.inl ⟨g0, g1, g2, h3, h4, c5z⟩
    · have g0 : (S.filter (fun k => v k = 0)).card = 1 := by omega
      have g1 : (S.filter (fun k => v k = 1)).card = 3 := by omega
      have g2 : (S.filter (fun k => v k = 2)).card = 1 := by omega
      exact Or.inr (Or.inl ⟨g0, g1, g2, h3, h4, c5z⟩)
  · have c3split : (S.filter (fun k => v k = 3)).card = 0 ∨
        (S.filter (fun k => v k = 3)).card = 1 := by omega
    rcases c3split with h3 | h3
    · have g0 : (S.filter (fun k => v k = 0)).card = 1 := by omega
      have g1 : (S.filter (fun k => v k = 1)).card = 2 := by omega
      have g2 : (S.filter (fun k => v k = 2)).card = 4 := by omega
      exact Or.inr (Or.inr (Or.inl ⟨g0, g1, g2, h3, h4, c5z⟩))
    · have g0 : (S.filter (fun k => v k = 0)).card = 0 := by omega
      have g1 : (S.filter (fun k => v k = 1)).card = 5 := by omega
      have g2 : (S.filter (fun k => v k = 2)).card = 1 := by omega
      exact Or.inr (Or.inr (Or.inr ⟨g0, g1, g2, h3, h4, c5z⟩))

