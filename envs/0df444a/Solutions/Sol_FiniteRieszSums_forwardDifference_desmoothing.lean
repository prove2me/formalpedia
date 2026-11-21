-- Prove2me | solution 1 for FiniteRieszSums.forwardDifference_desmoothing
-- status  : ACCEPTED   (prove)
-- author  : @Yi
-- created : 2026-11-21T00:26:25.832229+00:00
-- url     : https://prove2.me/submissions/a866854a-0661-4ef0-ba53-7453b422d02f

import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Ring

open Finset Function

private def sums (a : ℕ → ℂ) (m t : ℕ) :=
  ∑ n ∈ range (t+1), a n * ((t:ℂ)-n)^m

private def frozen (a : ℕ → ℂ) (m x t : ℕ) :=
  ∑ n ∈ range (x+1), a n * ((t:ℂ)-n)^m

private def weight (m j : ℕ) : ℤ := (-1:ℤ)^(m-j) * m.choose j

private theorem freeze_error (a : ℕ → ℂ) (ha : ∀ n, ‖a n‖ ≤ 1) (m x t : ℕ) (hxt : x ≤ t) :
    ‖sums a m t - frozen a m x t‖ ≤ ((t-x : ℕ):ℝ)^(m+1) := by
  let f := fun n : ℕ => a n * ((t:ℂ)-n)^m
  change ‖(∑ n ∈ range (t+1), f n) - ∑ n ∈ range (x+1), f n‖ ≤ _
  rw [show t+1 = (x+1)+(t-x) by omega, sum_range_add, add_sub_cancel_left]
  calc
    _ ≤ ∑ j ∈ range (t-x), ‖f (x+1+j)‖ := norm_sum_le _ _
    _ ≤ ∑ _j ∈ range (t-x), ((t-x : ℕ):ℝ)^m := by
      apply sum_le_sum
      intro j hj
      have hjt : x+1+j ≤ t := by have := mem_range.mp hj; omega
      simp only [f, norm_mul, norm_pow, ← Nat.cast_sub hjt, Complex.norm_natCast]
      calc
        _ ≤ 1 * ((t - (x+1+j) : ℕ):ℝ)^m := mul_le_mul_of_nonneg_right (ha _) (by positivity)
        _ ≤ _ := by
          rw [one_mul]
          gcongr
          omega
    _ = _ := by simp [pow_succ, mul_comm]

private theorem difference_monomial (m : ℕ) (z d : ℂ) (hd : d ≠ 0) :
    ∑ j ∈ range (m+1), weight m j • (z+(j:ℂ)*d)^m = (m.factorial:ℂ)*d^m := by
  have hval := fwdDiff_iter_eq_sum_shift (1:ℂ) (fun w : ℂ => w ^ m) m (z/d)
  rw [fwdDiff_iter_eq_factorial] at hval
  have hfact : (m.factorial:ℂ) = ∑ j ∈ range (m+1), weight m j • (z/d+(j:ℂ))^m := by
    simpa [weight] using hval
  rw [hfact, sum_mul]
  apply sum_congr rfl
  intro j _
  simp only [zsmul_eq_mul, mul_assoc, ← mul_pow]
  rw [add_mul, div_mul_cancel₀ _ hd]

private theorem frozen_difference (a : ℕ → ℂ) (m x h : ℕ) (hh : 0 < h) :
    (∑ j ∈ range (m+1), weight m j • frozen a m x (x+j*h)) =
    ((m.factorial:ℂ) * (h:ℂ)^m) * ∑ n ∈ range (x+1), a n := by
  unfold frozen
  simp_rw [Finset.smul_sum]
  rw [Finset.sum_comm, Finset.mul_sum]
  apply sum_congr rfl
  intro n _
  rw [← difference_monomial m ((x:ℂ)-n) h (by exact_mod_cast hh.ne'), Finset.sum_mul]
  apply sum_congr rfl
  intro j _
  push_cast
  simp only [zsmul_eq_mul]
  rw [show (x:ℂ)+j*h-n = x-n+j*h by ring]
  ring

private theorem weight_sum (m : ℕ) :
    ∑ j ∈ range (m+1), (m.choose j : ℝ) = (2:ℝ)^m := by
  exact_mod_cast Nat.sum_range_choose m

theorem solution (a : ℕ → ℂ) (ha : ∀ n, ‖a n‖ ≤ 1) (m x h : ℕ) (hh : 0 < h) :
    let R := fun t : ℕ => ∑ n ∈ Finset.range (t+1), a n * ((t:ℂ)-n)^m
    let S := ∑ n ∈ Finset.range (x+1), a n
    ‖(fwdDiff h)^[m] R x - ((m.factorial:ℂ)*(h:ℂ)^m)*S‖ ≤
      (2:ℝ)^m * ((m:ℝ)*h)^(m+1) := by
  change ‖(fwdDiff h)^[m] (sums a m) x - _‖ ≤ _
  rw [fwdDiff_iter_eq_sum_shift, ← frozen_difference a m x h hh]
  simp only [nsmul_eq_mul]
  change ‖(∑ j ∈ range (m+1), weight m j • sums a m (x+j*h)) - _‖ ≤ _
  rw [← sum_sub_distrib]
  calc
    _ ≤ ∑ j ∈ range (m+1), ‖weight m j • sums a m (x+j*h) - weight m j • frozen a m x (x+j*h)‖ := norm_sum_le _ _
    _ ≤ ∑ j ∈ range (m+1), (m.choose j : ℝ) * ((m:ℝ)*h)^(m+1) := by
      apply sum_le_sum
      intro j hj
      rw [← smul_sub, zsmul_eq_mul, norm_mul]
      have hw : ‖(weight m j : ℂ)‖ = (m.choose j : ℝ) := by simp [weight]
      rw [hw]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have he := freeze_error a ha m x (x+j*h) (by omega)
      simp only [Nat.add_sub_cancel_left, Nat.cast_mul] at he
      apply he.trans
      gcongr
      exact_mod_cast Nat.lt_succ_iff.mp (mem_range.mp hj)
    _ = _ := by rw [← sum_mul, weight_sum]
