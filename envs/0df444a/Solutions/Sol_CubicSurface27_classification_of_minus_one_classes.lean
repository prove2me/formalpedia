-- Prove2me | solution 1 for CubicSurface27.classification_of_minus_one_classes
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-21T01:34:20.059721+00:00
-- url     : https://prove2.me/submissions/cc11b3f4-73c3-4f14-a7c8-b8ee52725749

import Mathlib
open Finset

theorem solution (a : ℤ) (b : Fin 6 → ℤ)
    (ha : 0 < a) (hb : ∀ i, 0 ≤ b i)
    (hself : a ^ 2 - ∑ i : Fin 6, (b i) ^ 2 = -1)
    (hadj : 3 * a - ∑ i : Fin 6, b i = 1) :
    (a = 1 ∧ ∃ i j : Fin 6, i ≠ j ∧ b = fun k => if k = i ∨ k = j then 1 else 0) ∨
    (a = 2 ∧ ∃ i : Fin 6, b = fun k => if k = i then 0 else 1) := by
  -- basic rewrites of the two hypotheses
  have hQ : ∑ i : Fin 6, (b i) ^ 2 = a ^ 2 + 1 := by linarith
  have hS : ∑ i : Fin 6, b i = 3 * a - 1 := by linarith
  -- Cauchy–Schwarz gives a < 3
  have hcs : (3 * a - 1) ^ 2 ≤ 6 * (a ^ 2 + 1) := by
    have h := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin 6))) (f := b)
    have h' : (∑ i : Fin 6, b i) ^ 2 ≤ 6 * ∑ i : Fin 6, (b i) ^ 2 := by simpa using h
    rwa [hS, hQ] at h'
  have ha2 : a = 1 ∨ a = 2 := by
    have h3 : a < 3 := by nlinarith
    omega
  -- each b i satisfies b i ^ 2 ≥ b i
  have hterm : ∀ i, 0 ≤ (b i) ^ 2 - b i := by
    intro i
    rcases eq_or_lt_of_le (hb i) with h | h
    · simp [← h]
    · have h2 : (0 : ℤ) ≤ b i - 1 := by linarith
      nlinarith [mul_nonneg (hb i) h2]
  -- if the sum of squares equals the sum then every entry is 0 or 1
  have hb01_of : (∑ i : Fin 6, (b i) ^ 2) = (∑ i : Fin 6, b i) → ∀ i, b i = 0 ∨ b i = 1 := by
    intro hEq i
    have hz : ∑ j : Fin 6, ((b j) ^ 2 - b j) = 0 := by
      rw [Finset.sum_sub_distrib, hEq]; ring
    have hsingle : (b i) ^ 2 - b i ≤ ∑ j : Fin 6, ((b j) ^ 2 - b j) :=
      Finset.single_le_sum (fun j _ => hterm j) (Finset.mem_univ i)
    rw [hz] at hsingle
    have hper : (b i) ^ 2 - b i = 0 := by linarith [hterm i]
    have hmul : b i * (b i - 1) = 0 := by
      have : b i * (b i - 1) = (b i) ^ 2 - b i := by ring
      rw [this, hper]
    rcases mul_eq_zero.mp hmul with h0 | h1
    · exact Or.inl h0
    · exact Or.inr (by linarith)
  -- indicator sums are cardinalities
  have hboole (p : Fin 6 → Prop) [DecidablePred p] :
      (∑ i : Fin 6, (if p i then (1 : ℤ) else 0)) = ((Finset.univ.filter p).card : ℤ) := by
    simpa using (Finset.sum_boole (R := ℤ) p (Finset.univ : Finset (Fin 6)))
  rcases ha2 with h1 | h2
  · -- case a = 1
    left
    refine ⟨h1, ?_⟩
    have hQ1 : ∑ i : Fin 6, (b i) ^ 2 = 2 := by rw [hQ, h1]; norm_num
    have hS1 : ∑ i : Fin 6, b i = 2 := by rw [hS, h1]; norm_num
    have hb01 : ∀ i, b i = 0 ∨ b i = 1 := hb01_of (by rw [hQ1, hS1])
    have hsum1 : ∑ i : Fin 6, (if b i = 1 then (1 : ℤ) else 0) = ∑ i : Fin 6, b i := by
      apply Finset.sum_congr rfl
      intro i _
      rcases hb01 i with h | h <;> simp [h]
    have hcardZ : ((Finset.univ.filter (fun i : Fin 6 => b i = 1)).card : ℤ) = 2 := by
      rw [← hboole (fun i : Fin 6 => b i = 1)]
      rw [hsum1, hS1]
    have hcard : (Finset.univ.filter (fun i : Fin 6 => b i = 1)).card = 2 := by
      exact_mod_cast hcardZ
    obtain ⟨i, j, hij, hT⟩ := Finset.card_eq_two.mp hcard
    refine ⟨i, j, hij, ?_⟩
    have hk : ∀ k : Fin 6, (b k = 1 ↔ (k = i ∨ k = j)) := by
      intro k
      have hmem : k ∈ (Finset.univ.filter (fun x : Fin 6 => b x = 1)) ↔
          k ∈ ({i, j} : Finset (Fin 6)) := by rw [hT]
      simpa using hmem
    funext k
    show b k = if k = i ∨ k = j then (1 : ℤ) else 0
    by_cases h : k = i ∨ k = j
    · rw [if_pos h]; exact (hk k).mpr h
    · rw [if_neg h]
      rcases hb01 k with h0 | h0
      · exact h0
      · exact absurd ((hk k).mp h0) h
  · -- case a = 2
    right
    refine ⟨h2, ?_⟩
    have hQ2 : ∑ i : Fin 6, (b i) ^ 2 = 5 := by rw [hQ, h2]; norm_num
    have hS2 : ∑ i : Fin 6, b i = 5 := by rw [hS, h2]; norm_num
    have hb01 : ∀ i, b i = 0 ∨ b i = 1 := hb01_of (by rw [hQ2, hS2])
    have hsum0 : ∑ i : Fin 6, (if b i = 0 then (1 : ℤ) else 0) = ∑ i : Fin 6, (1 - b i) := by
      apply Finset.sum_congr rfl
      intro i _
      rcases hb01 i with h | h <;> simp [h]
    have hcardZ : ((Finset.univ.filter (fun i : Fin 6 => b i = 0)).card : ℤ) = 1 := by
      rw [← hboole (fun i : Fin 6 => b i = 0)]
      rw [hsum0, Finset.sum_sub_distrib]
      simp [hS2]
    have hcard : (Finset.univ.filter (fun i : Fin 6 => b i = 0)).card = 1 := by
      exact_mod_cast hcardZ
    obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hcard
    refine ⟨i, ?_⟩
    have hk : ∀ k : Fin 6, (b k = 0 ↔ k = i) := by
      intro k
      have hmem : k ∈ (Finset.univ.filter (fun x : Fin 6 => b x = 0)) ↔
          k ∈ ({i} : Finset (Fin 6)) := by rw [hi]
      simpa using hmem
    funext k
    show b k = if k = i then (0 : ℤ) else 1
    by_cases h : k = i
    · rw [if_pos h]; exact (hk k).mpr h
    · rw [if_neg h]
      rcases hb01 k with h0 | h0
      · exact absurd ((hk k).mp h0) h
      · exact h0
