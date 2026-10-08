-- Prove2me | solution 1 for ConvexOptAlg.Ellipsoid.lemma_2_3_scalar
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T14:30:25.460255+00:00
-- url     : https://prove2.me/submissions/7e3f718d-0697-4ec3-bf76-e84fea1160fc

import Mathlib
import Definitions.Def_ConvexOptAlg_Ellipsoid_Defs

namespace D4ee8b7fAux

/-- For `0 < x < 1` with `n * x = 1`: `x ≤ (n+1) log(1+x) + (n-1) log(1-x)`
via the artanh and `-log(1-y)` series. -/
lemma key (n : ℝ) (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) (hnx : n * x = 1) :
    x ≤ (Real.log (1 + x) - Real.log (1 - x)) + n * Real.log (1 - x ^ 2) := by
  have hax : |x| < 1 := by rw [abs_of_pos hx0]; exact hx1
  have hx2 : |x ^ 2| < 1 := by
    rw [abs_of_pos (by positivity)]; nlinarith
  have h1 := Real.hasSum_pow_div_log_of_abs_lt_one hx2
  have h2 := Real.hasSum_log_sub_log_of_abs_lt_one hax
  have h3 := h2.sub (h1.mul_left n)
  have hterm : ∀ k : ℕ, (2 : ℝ) * (1 / (2 * k + 1)) * x ^ (2 * k + 1)
      - n * ((x ^ 2) ^ (k + 1) / ((k : ℝ) + 1))
      = x ^ (2 * k + 1) / ((2 * k + 1) * ((k : ℝ) + 1)) := by
    intro k
    have hk1 : (0 : ℝ) < 2 * k + 1 := by positivity
    have hk2 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    have : (x ^ 2) ^ (k + 1) = x ^ (2 * k + 1) * x := by
      rw [← pow_mul, ← pow_succ]; ring_nf
    rw [this]
    field_simp
    have : n * (x ^ (2 * k + 1) * x) = x ^ (2 * k + 1) := by
      rw [mul_comm (x ^ (2 * k + 1)) x, ← mul_assoc, hnx, one_mul]
    nlinarith [this]
  have hle := sum_le_hasSum (Finset.range 1) (fun k _ => by
    rw [hterm k]; positivity) h3
  simp only [Finset.sum_range_one] at hle
  rw [hterm 0] at hle
  simp at hle
  linarith

end D4ee8b7fAux

theorem solution (n : ℕ) (hn : 2 ≤ n) :
    Real.exp (1 / (n : ℝ)) ≤ (1 + 1 / (n : ℝ)) ^ 2 * (1 - 1 / (n : ℝ) ^ 2) ^ (n - 1) := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  set x : ℝ := 1 / (n : ℝ) with hxdef
  have hx0 : 0 < x := by positivity
  have hx1 : x < 1 := by rw [hxdef, div_lt_one (by linarith)]; linarith
  have hnx : (n : ℝ) * x = 1 := by rw [hxdef]; field_simp
  have hk := D4ee8b7fAux.key (n : ℝ) x hx0 hx1 hnx
  have hpx : 0 < 1 + x := by linarith
  have hmx : 0 < 1 - x := by linarith
  have hsq : (1 - 1 / (n : ℝ) ^ 2) = (1 + x) * (1 - x) := by rw [hxdef]; ring
  have hsq2 : 1 - x ^ 2 = (1 + x) * (1 - x) := by ring
  rw [hsq]
  have hpos : 0 < (1 + x) ^ 2 * ((1 + x) * (1 - x)) ^ (n - 1) := by positivity
  rw [← Real.exp_log hpos]
  apply Real.exp_le_exp.mpr
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow,
    Real.log_mul hpx.ne' hmx.ne']
  rw [hsq2, Real.log_mul hpx.ne' hmx.ne'] at hk
  have hc : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; simp
  rw [hc]
  push_cast
  nlinarith [hk]
