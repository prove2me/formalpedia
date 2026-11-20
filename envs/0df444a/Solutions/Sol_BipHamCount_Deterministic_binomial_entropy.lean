-- Prove2me | solution 1 for BipHamCount.Deterministic.binomial_entropy
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-19T14:59:53.250967+00:00
-- url     : https://prove2.me/submissions/59218230-b309-4b54-91e7-c9753d17fbda

import Mathlib

open Real Finset

theorem solution (m q : ℕ) (hq : q ≤ m) :
    (m.choose q : ℝ) ≤ Real.exp ((m : ℝ) * Real.binEntropy ((q : ℝ) / m)) := by
  rcases Nat.eq_zero_or_pos q with rfl | hq0
  · simp
  rcases eq_or_lt_of_le hq with rfl | hqm
  · have hm : (q : ℝ) ≠ 0 := by exact_mod_cast hq0.ne'
    simp [div_self hm]
  set p : ℝ := (q : ℝ) / m with hp
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (lt_of_lt_of_le hq0 hq)
  have hp0 : 0 < p := div_pos (by exact_mod_cast hq0) hm0
  have hp1 : p < 1 := (div_lt_one hm0).mpr (by exact_mod_cast hqm)
  have h1p : 0 < 1 - p := by linarith
  -- one term of the binomial expansion
  have hterm : (m.choose q : ℝ) * (p ^ q * (1 - p) ^ (m - q)) ≤ 1 := by
    have hexp : ∑ j ∈ range (m + 1), p ^ j * (1 - p) ^ (m - j) * (m.choose j : ℝ) = 1 := by
      rw [← add_pow, add_sub_cancel, one_pow]
    refine le_trans ?_ hexp.le
    have := single_le_sum (s := range (m + 1))
      (f := fun j => p ^ j * (1 - p) ^ (m - j) * (m.choose j : ℝ))
      (fun j _ => by positivity) (mem_range.mpr (Nat.lt_succ_of_le hq))
    simpa [mul_comm, mul_left_comm, mul_assoc] using this
  -- the exponential identity
  have hident : Real.exp ((m : ℝ) * Real.binEntropy p) = (p ^ q * (1 - p) ^ (m - q))⁻¹ := by
    have hq' : (m : ℝ) * p = q := by rw [hp]; field_simp
    have hmq : (m : ℝ) * (1 - p) = ((m - q : ℕ) : ℝ) := by
      rw [Nat.cast_sub hq, mul_sub, mul_one, hq']
    have hb : Real.binEntropy p = -p * Real.log p - (1 - p) * Real.log (1 - p) := by
      unfold Real.binEntropy; simp only [Real.log_inv]; ring
    rw [hb, ← Real.exp_log (by positivity : (0 : ℝ) < (p ^ q * (1 - p) ^ (m - q))⁻¹)]
    congr 1
    rw [Real.log_inv, Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
    have e1 : (m : ℝ) * (-p * Real.log p - (1 - p) * Real.log (1 - p))
        = -((m * p) * Real.log p + (m * (1 - p)) * Real.log (1 - p)) := by ring
    rw [e1, hq', hmq]
  rw [hident]
  have hx : 0 < p ^ q * (1 - p) ^ (m - q) := by positivity
  calc (m.choose q : ℝ) = ((m.choose q : ℝ) * (p ^ q * (1 - p) ^ (m - q))) * (p ^ q * (1 - p) ^ (m - q))⁻¹ := by
        field_simp
    _ ≤ 1 * (p ^ q * (1 - p) ^ (m - q))⁻¹ := by gcongr
    _ = _ := one_mul _
