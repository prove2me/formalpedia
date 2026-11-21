-- Prove2me | solution 1 for GaussMixGated.ExactReal.Supplement.lemma_A_2
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-21T03:52:50.003116+00:00
-- url     : https://prove2.me/submissions/310e5260-8406-4eae-9334-1139203ace61

import Mathlib

open Finset

theorem solution {ι : Type*} [Fintype ι] (N : ℝ) (t : ℕ) (h : ℝ)
    (r : ι → ℕ) (c : ι → ℝ) (x xhat : (l : ι) → Fin (r l) → ℝ)
    (hN2 : 2 ≤ N) (hNt : (t : ℝ) ≤ N) (ht : 2 ≤ t)
    (hr : ∀ l, r l ≤ t) (hc : ∑ l, |c l| ≤ N ^ (2 * t))
    (hh0 : 0 ≤ h) (hh1 : h ≤ 1)
    (hx : ∀ l j, |x l j| ≤ N) (hxh : ∀ l j, |xhat l j - x l j| ≤ h) :
    |∑ l, c l * ∏ j, x l j| ≤ N ^ (3 * t) ∧
      |(∑ l, c l * ∏ j, xhat l j) - (∑ l, c l * ∏ j, x l j)| ≤
        N ^ (4 * t) * h := by
  have hN1 : (1 : ℝ) ≤ N := by linarith
  have hNpos : (0 : ℝ) < N := by linarith
  -- Telescoping bound: |∏ xhat - ∏ x| ≤ N^(2n) * h
  have key : ∀ (n : ℕ) (a b : Fin n → ℝ),
      (∀ i, |b i| ≤ N + 1) → (∀ i, |b i - a i| ≤ h) → (∀ i, |a i| ≤ N) →
      |(∏ i, b i) - (∏ i, a i)| ≤ N ^ (2 * n) * h := by
    intro n
    induction n with
    | zero =>
      intro a b _ _ _
      simpa using hh0
    | succ n ih =>
      intro a b hb hba ha
      rw [Fin.prod_univ_succ (f := b), Fin.prod_univ_succ (f := a)]
      have hb2 : ∀ i, |b i| ≤ N ^ 2 := by
        intro i
        have h1 : N + 1 ≤ N ^ 2 := by nlinarith
        linarith [hb i]
      have hAsucc : |∏ i : Fin n, b i.succ| ≤ N ^ (2 * n) := by
        have h1 : |∏ i : Fin n, b i.succ| = ∏ i : Fin n, |b i.succ| := by
          rw [Finset.abs_prod]
        rw [h1]
        calc ∏ i : Fin n, |b i.succ| ≤ ∏ i : Fin n, N ^ 2 := by
              apply Finset.prod_le_prod
              · intro i _; positivity
              · intro i _; exact hb2 _
          _ = (N ^ 2) ^ n := by simp
          _ = N ^ (2 * n) := by rw [pow_mul]
      have hIH : |(∏ i : Fin n, b i.succ) - (∏ i : Fin n, a i.succ)| ≤
          N ^ (2 * n) * h :=
        ih (fun i => a i.succ) (fun i => b i.succ)
          (fun i => hb i.succ) (fun i => hba i.succ) (fun i => ha i.succ)
      have hstep : |b 0 * ∏ i : Fin n, b i.succ - a 0 * ∏ i : Fin n, a i.succ|
          ≤ h * N ^ (2 * n) + N * (N ^ (2 * n) * h) := by
        calc |b 0 * ∏ i : Fin n, b i.succ - a 0 * ∏ i : Fin n, a i.succ|
            = |(b 0 - a 0) * (∏ i : Fin n, b i.succ) +
                a 0 * ((∏ i : Fin n, b i.succ) - (∏ i : Fin n, a i.succ))| := by
              congr 1
              ring
          _ ≤ |(b 0 - a 0) * (∏ i : Fin n, b i.succ)| +
                |a 0 * ((∏ i : Fin n, b i.succ) - (∏ i : Fin n, a i.succ))| := abs_add_le _ _
          _ = |b 0 - a 0| * |∏ i : Fin n, b i.succ| +
                |a 0| * |(∏ i : Fin n, b i.succ) - (∏ i : Fin n, a i.succ)| := by
              rw [abs_mul, abs_mul]
          _ ≤ h * N ^ (2 * n) + N * (N ^ (2 * n) * h) := by
              apply add_le_add
              · exact mul_le_mul (hba 0) hAsucc (abs_nonneg _) hh0
              · exact mul_le_mul (ha 0) hIH (abs_nonneg _) hNpos.le
      refine le_trans hstep ?_
      have hp : (0 : ℝ) < N ^ (2 * n) := pow_pos hNpos _
      have hMh : (0 : ℝ) ≤ N ^ (2 * n) * h := by positivity
      have hquad : (0 : ℝ) ≤ N ^ 2 - N - 1 := by nlinarith
      have he : 2 * (n + 1) = 2 * n + 2 := by ring
      rw [he, pow_add]
      nlinarith [mul_nonneg hMh hquad]
  -- per-l bound
  have hper : ∀ l, |(∏ j : Fin (r l), xhat l j) - (∏ j : Fin (r l), x l j)| ≤
      N ^ (2 * t) * h := by
    intro l
    have hb : ∀ j, |xhat l j| ≤ N + 1 := by
      intro j
      have he : x l j + (xhat l j - x l j) = xhat l j := by ring
      calc |xhat l j| = |x l j + (xhat l j - x l j)| := by rw [he]
        _ ≤ |x l j| + |xhat l j - x l j| := abs_add_le _ _
        _ ≤ N + 1 := by linarith [hx l j, hxh l j]
    have hk := key (r l) (x l) (xhat l) hb (fun j => hxh l j) (fun j => hx l j)
    refine le_trans hk ?_
    apply mul_le_mul_of_nonneg_right _ hh0
    exact pow_le_pow_right₀ hN1 (Nat.mul_le_mul_left 2 (hr l))
  constructor
  · -- Conjunct 1
    calc |∑ l, c l * ∏ j, x l j|
        ≤ ∑ l, |c l * ∏ j, x l j| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ l, |c l| * ∏ j : Fin (r l), |x l j| := by
          apply Finset.sum_congr rfl
          intro l _
          rw [abs_mul, Finset.abs_prod]
      _ ≤ ∑ l, |c l| * N ^ t := by
          apply Finset.sum_le_sum
          intro l _
          apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
          calc ∏ j : Fin (r l), |x l j| ≤ ∏ j : Fin (r l), N := by
                apply Finset.prod_le_prod
                · intro j _; positivity
                · intro j _; exact hx l j
            _ = N ^ (r l) := by simp
            _ ≤ N ^ t := pow_le_pow_right₀ hN1 (hr l)
      _ = N ^ t * ∑ l, |c l| := by
          rw [← Finset.sum_mul]
          ring
      _ ≤ N ^ t * N ^ (2 * t) := by
          apply mul_le_mul_of_nonneg_left hc (by positivity)
      _ = N ^ (3 * t) := by
          rw [← pow_add]
          congr 1
          ring
  · -- Conjunct 2
    have hsum_eq : (∑ l, c l * ∏ j, xhat l j) - (∑ l, c l * ∏ j, x l j)
        = ∑ l, c l * ((∏ j, xhat l j) - (∏ j, x l j)) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro l _
      ring
    rw [hsum_eq]
    calc |∑ l, c l * ((∏ j : Fin (r l), xhat l j) - (∏ j : Fin (r l), x l j))|
        ≤ ∑ l, |c l * ((∏ j : Fin (r l), xhat l j) - (∏ j : Fin (r l), x l j))| :=
          Finset.abs_sum_le_sum_abs _ _
      _ = ∑ l, |c l| * |(∏ j : Fin (r l), xhat l j) - (∏ j : Fin (r l), x l j)| := by
          apply Finset.sum_congr rfl
          intro l _
          rw [abs_mul]
      _ ≤ ∑ l, |c l| * (N ^ (2 * t) * h) := by
          apply Finset.sum_le_sum
          intro l _
          exact mul_le_mul_of_nonneg_left (hper l) (abs_nonneg _)
      _ = (∑ l, |c l|) * (N ^ (2 * t) * h) := by rw [Finset.sum_mul]
      _ ≤ N ^ (2 * t) * (N ^ (2 * t) * h) := by
          apply mul_le_mul_of_nonneg_right hc
          positivity
      _ = N ^ (4 * t) * h := by
          rw [← mul_assoc, ← pow_add]
          congr 1
          ring
