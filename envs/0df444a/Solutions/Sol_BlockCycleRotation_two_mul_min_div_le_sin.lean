-- Prove2me | solution 1 for BlockCycleRotation.two_mul_min_div_le_sin
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-05T10:28:22.752123+00:00
-- url     : https://prove2.me/submissions/2921d5d8-7a16-45df-850e-d802cf14a2e9

import Definitions.Def_BlockCycleRotation_ExpSum
import Mathlib

open Real Finset

namespace BlockCycleRotation

@[simp]
theorem norm_e (θ : ℝ) : ‖e θ‖ = 1 := Complex.norm_exp_ofReal_mul_I θ

@[simp]
theorem norm_e_pow (θ : ℝ) (n : ℕ) : ‖e θ ^ n‖ = 1 := by
  rw [norm_pow, norm_e, one_pow]

end BlockCycleRotation

open BlockCycleRotation in
/-- **Jordan's inequality at a root of unity.**  For `0 < m < a`,
`2 · min(m, a-m) / a ≤ sin (π m / a)`.

The two cases are `m ≤ a/2`, where Jordan applies directly, and `m > a/2`, where
it applies after reflecting via `sin (π - x) = sin x`. -/
theorem solution {a m : ℕ} (h0 : 0 < m) (hma : m < a) :
    2 * ((min m (a - m) : ℕ) : ℝ) / (a : ℝ) ≤ Real.sin (π * m / a):= by
  have hapos : 0 < a := lt_trans h0 hma
  have ha : (0 : ℝ) < a := by exact_mod_cast hapos
  have hpi := Real.pi_pos
  have hmle : (m : ℝ) ≤ (a : ℝ) := by exact_mod_cast hma.le
  rcases le_or_gt (2 * m) a with hcase | hcase
  · -- `min = m`, and `π m / a ≤ π / 2`
    have hmin : min m (a - m) = m := by omega
    rw [hmin]
    have hx0 : 0 ≤ π * m / a := by positivity
    have hx1 : π * (m : ℝ) / a ≤ π / 2 := by
      rw [div_le_div_iff₀ ha (by norm_num)]
      have h2m : (2 : ℝ) * m ≤ a := by exact_mod_cast hcase
      nlinarith
    have hj := Real.mul_le_sin hx0 hx1
    have hrw : 2 / π * (π * (m : ℝ) / a) = 2 * (m : ℝ) / a := by field_simp
    rw [hrw] at hj
    exact hj
  · -- `min = a - m`, and reflect
    have hmin : min m (a - m) = a - m := by omega
    have hsub : ((a - m : ℕ) : ℝ) = (a : ℝ) - m := by rw [Nat.cast_sub hma.le]
    have hd : (0 : ℝ) ≤ (a : ℝ) - m := by linarith
    rw [hmin, hsub]
    have hkey : π * (m : ℝ) / a = π - π * ((a : ℝ) - m) / a := by
      field_simp
      ring
    rw [hkey, Real.sin_pi_sub]
    have hx0 : 0 ≤ π * ((a : ℝ) - m) / a := div_nonneg (mul_nonneg hpi.le hd) ha.le
    have hx1 : π * ((a : ℝ) - m) / a ≤ π / 2 := by
      rw [div_le_div_iff₀ ha (by norm_num)]
      have h2m : (a : ℝ) < 2 * m := by exact_mod_cast hcase
      nlinarith
    have hj := Real.mul_le_sin hx0 hx1
    have hrw : 2 / π * (π * ((a : ℝ) - m) / a) = 2 * ((a : ℝ) - m) / a := by field_simp
    rw [hrw] at hj
    exact hj
