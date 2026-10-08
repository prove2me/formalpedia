-- Prove2me | solution 1 for EmpiricalBernstein.SVP.corollary_9
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T19:48:02.944962+00:00
-- url     : https://prove2.me/submissions/30f63d8a-29ed-4a88-a015-6400f2da27ed

import Mathlib
open scoped BigOperators

private lemma rotate_sum {n : ℕ} (f : Fin n → Fin n → Fin n → ℝ) :
    (∑ k, ∑ j, ∑ i, f j i k) = ∑ k, ∑ j, ∑ i, f k j i := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.sum_comm]

theorem solution {n : ℕ} (x : Fin n → ℝ) (hx : ∀ i, x i ∈ Set.Icc (0 : ℝ) 1) :
    (1 / (n : ℝ)) * ∑ k, ((1 / (n : ℝ)) * ∑ j, (x k - x j) ^ 2) ^ 2
      ≤ 1 / (2 * (n : ℝ) ^ 2) * ∑ k, ∑ j, (x k - x j) ^ 2 := by
  by_cases hn : n = 0
  · subst n; simp
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero hn)
  let A : ℝ := ∑ k, ∑ j, ∑ i, (x k - x j) ^ 2 * (x k - x i) ^ 2
  let D : ℝ := ∑ k, ∑ j, (x k - x j) ^ 4
  have hpoly (a b c : ℝ) :
      2 * ((a-b)^2*(a-c)^2 + (b-c)^2*(b-a)^2 + (c-a)^2*(c-b)^2) =
      (a-b)^4 + (b-c)^4 + (c-a)^4 := by ring
  have hb : (∑ k, ∑ j, ∑ i, (x j-x i)^2*(x j-x k)^2) = A := by
    dsimp [A]
    exact rotate_sum (fun k j i => (x k-x j)^2*(x k-x i)^2)
  have hc : (∑ k, ∑ j, ∑ i, (x i-x k)^2*(x i-x j)^2) = A := by
    calc
      _ = ∑ k, ∑ j, ∑ i, (x j-x i)^2*(x j-x k)^2 :=
        rotate_sum (fun k j i => (x j-x i)^2*(x j-x k)^2)
      _ = A := hb
  have hd1 : (∑ k, ∑ j, ∑ i : Fin n, (x k-x j)^4) = (n : ℝ) * D := by
    simp [D, Finset.mul_sum, mul_comm]
  have hd2 : (∑ k : Fin n, ∑ j, ∑ i : Fin n, (x j-x i)^4) = (n : ℝ) * D := by
    simpa [D] using congrArg (fun z : ℝ => z) (show (∑ k : Fin n, D) = (n : ℝ) * D by simp)
  have hd3 : (∑ k, ∑ j : Fin n, ∑ i : Fin n, (x i-x k)^4) = (n : ℝ) * D := by
    calc
      _ = ∑ k : Fin n, ∑ j, ∑ i : Fin n, (x j-x i)^4 := rotate_sum (fun k j i => (x j-x i)^4)
      _ = _ := hd2
  have hid : 2 * (A + A + A) = (n : ℝ) * D + (n : ℝ) * D + (n : ℝ) * D := by
    have h : (∑ k, ∑ j, ∑ i, 2 * ((x k-x j)^2*(x k-x i)^2 +
        (x j-x i)^2*(x j-x k)^2 + (x i-x k)^2*(x i-x j)^2)) =
        ∑ k, ∑ j, ∑ i, ((x k-x j)^4 + (x j-x i)^4 + (x i-x k)^4) := by
      apply Finset.sum_congr rfl; intro k hk
      apply Finset.sum_congr rfl; intro j hj
      apply Finset.sum_congr rfl; intro i hi
      exact hpoly (x k) (x j) (x i)
    have hl : (∑ k, ∑ j, ∑ i, 2 * ((x k-x j)^2*(x k-x i)^2 +
        (x j-x i)^2*(x j-x k)^2 + (x i-x k)^2*(x i-x j)^2)) =
        2 * (A + (∑ k, ∑ j, ∑ i, (x j-x i)^2*(x j-x k)^2) +
        (∑ k, ∑ j, ∑ i, (x i-x k)^2*(x i-x j)^2)) := by
      dsimp [A]
      simp only [Finset.mul_sum, Finset.sum_add_distrib, mul_add]
    rw [hl, hb, hc] at h
    simp only [Finset.sum_add_distrib] at h
    rwa [hd1, hd2, hd3] at h
  have hD : D ≤ ∑ k, ∑ j, (x k-x j)^2 := by
    apply Finset.sum_le_sum; intro k hk
    apply Finset.sum_le_sum; intro j hj
    have h1 := hx k; have h2 := hx j
    have hs : (x k-x j)^2 ≤ 1 := by
      have hl : 0 ≤ 1 - (x k-x j) := by linarith [h1.2, h2.1]
      have hr : 0 ≤ 1 + (x k-x j) := by linarith [h1.1, h2.2]
      nlinarith [mul_nonneg hl hr]
    nlinarith [sq_nonneg (x k-x j), mul_nonneg (sq_nonneg (x k-x j)) (sub_nonneg.mpr hs)]
  have hexpand : (∑ k, (∑ j, (x k-x j)^2)^2) = A := by
    dsimp [A]
    apply Finset.sum_congr rfl; intro k hk
    rw [pow_two, Finset.sum_mul]
    apply Finset.sum_congr rfl; intro j hj
    rw [Finset.mul_sum]
  simp_rw [mul_pow]
  rw [← Finset.mul_sum, hexpand]
  have hA : 2 * A = (n : ℝ) * D := by linarith [hid]
  have hm := mul_le_mul_of_nonneg_left hD hn0.le
  field_simp
  nlinarith

#print axioms solution
