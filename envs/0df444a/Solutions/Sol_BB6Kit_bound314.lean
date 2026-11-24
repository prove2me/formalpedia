-- Prove2me | solution 1 for BB6Kit.bound314
-- status  : ACCEPTED   (prove)
-- author  : @alon yuval
-- created : 2026-11-24T07:29:43.871803+00:00
-- url     : https://prove2.me/submissions/8988bc4c-0853-4042-9d88-5ffccd20ebac

import Mathlib

theorem solution (K L : ℕ) (ρ : ℝ) (hK : 3 ≤ K) (hL : 5 ≤ L) (hρ : 2 ≤ ρ) :
    ρ * ((K : ℝ) * ((K : ℝ) + 1) * L) / 8 * ρ ^ (-((K : ℝ) * L)) ≤ 0.001 := by
  have hx : 15 ≤ K * L := by nlinarith
  have hnat : ∀ x : ℕ, 15 ≤ x → 100 * x ^ 2 ≤ 3 * 2 ^ (x - 1) := by
    intro x hx
    induction x, hx using Nat.le_induction with
    | base => norm_num
    | succ n hn ih =>
      have e : n + 1 - 1 = (n - 1) + 1 := by omega
      rw [e, pow_succ (2:ℕ) (n - 1)]
      nlinarith [ih, Nat.mul_le_mul hn hn]
  have hpow : (100:ℝ) * ((K * L : ℕ) : ℝ) ^ 2 ≤ 3 * 2 ^ (K * L - 1) := by
    exact_mod_cast hnat (K * L) hx
  have hρ0 : 0 < ρ := by linarith
  have hxr : ((K : ℝ) * L) = ((K * L : ℕ) : ℝ) := by push_cast; ring
  rw [hxr, Real.rpow_neg hρ0.le, Real.rpow_natCast]
  have hsplit : ρ ^ (K * L) = ρ * ρ ^ (K * L - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have h2 : (2:ℝ) ^ (K * L - 1) ≤ ρ ^ (K * L - 1) := pow_le_pow_left₀ (by norm_num) hρ _
  have hK3 : (3:ℝ) ≤ K := by exact_mod_cast hK
  have hL5 : (5:ℝ) ≤ L := by exact_mod_cast hL
  have hC : (K : ℝ) * ((K : ℝ) + 1) * L ≤ 4 / 15 * ((K * L : ℕ) : ℝ) ^ 2 := by
    push_cast
    have h1a : (1:ℝ) / 3 ≤ 4 * (L : ℝ) / 15 - 1 := by linarith
    have h1 : (1:ℝ) ≤ (4 * (L : ℝ) / 15 - 1) * K := by
      have := mul_le_mul_of_nonneg_left h1a (by linarith : (0:ℝ) ≤ K)
      linarith
    have h3 : (0:ℝ) ≤ K * L := by positivity
    have h4 := mul_le_mul_of_nonneg_left h1 h3
    nlinarith
  rw [hsplit]
  have hP : 0 < ρ ^ (K * L - 1) := by positivity
  have e : ρ * ((K : ℝ) * ((K : ℝ) + 1) * L) / 8 * (ρ * ρ ^ (K * L - 1))⁻¹ =
      ((K : ℝ) * ((K : ℝ) + 1) * L) / (8 * ρ ^ (K * L - 1)) := by
    field_simp
  rw [e, div_le_iff₀ (by positivity)]
  linarith
