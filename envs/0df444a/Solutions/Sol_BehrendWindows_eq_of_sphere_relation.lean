-- Prove2me | solution 1 for BehrendWindows.eq_of_sphere_relation
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-11-21T01:56:11.134355+00:00
-- url     : https://prove2.me/submissions/9299a869-9c17-44d1-b203-3e70ec895874

import Mathlib

theorem solution {n : ℕ} (x y z : Fin n → ℕ)
    (hx : ∑ i, x i ^ 2 = ∑ i, y i ^ 2) (hz : ∑ i, z i ^ 2 = ∑ i, y i ^ 2)
    (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) (h : p • x + q • z = (p + q) • y) :
    x = z := by
  have hi : ∀ i, (p : ℤ) * x i + q * z i = (p + q) * y i := by
    intro i
    have := congrFun h i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this
    exact_mod_cast this
  have hX : ∑ i, ((x i : ℤ)) ^ 2 = ∑ i, ((y i : ℤ)) ^ 2 := by exact_mod_cast hx
  have hZ : ∑ i, ((z i : ℤ)) ^ 2 = ∑ i, ((y i : ℤ)) ^ 2 := by exact_mod_cast hz
  have hterm : ∀ i, ((p : ℤ) * q) * ((x i : ℤ) - z i) ^ 2 =
      (p + q) * p * (x i : ℤ) ^ 2 + (p + q) * q * (z i : ℤ) ^ 2 - (p + q) ^ 2 * (y i : ℤ) ^ 2 := by
    intro i
    linear_combination (-((p + q : ℤ) * y i + p * x i + q * z i)) * hi i
  have key : ∑ i, ((p : ℤ) * q) * ((x i : ℤ) - z i) ^ 2 = 0 := by
    rw [Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_sub_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, hX, hZ]
    ring
  have hpq : (0 : ℤ) < p * q := by positivity
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun i _ => by positivity)] at key
  funext i
  have := key i (Finset.mem_univ i)
  rcases mul_eq_zero.1 this with h0 | h0
  · exact absurd h0 hpq.ne'
  · have : (x i : ℤ) - z i = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h0
    exact_mod_cast sub_eq_zero.1 this
