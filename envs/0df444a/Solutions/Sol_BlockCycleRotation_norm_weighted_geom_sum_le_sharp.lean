-- Prove2me | solution 1 for BlockCycleRotation.norm_weighted_geom_sum_le_sharp
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-05T10:17:11.777292+00:00
-- url     : https://prove2.me/submissions/43f0c451-c58b-451d-b002-3bd96101e24c

import Definitions.Def_BlockCycleRotation_ExpSum
import Theorems.Thm_BlockCycleRotation_mul_abs_le_norm_e_sub_one
import Theorems.Thm_BlockCycleRotation_weighted_geom_sum_closed
import Mathlib

open Real Finset

namespace BlockCycleRotation

@[simp]
theorem norm_e (θ : ℝ) : ‖e θ‖ = 1 := Complex.norm_exp_ofReal_mul_I θ

@[simp]
theorem norm_e_pow (θ : ℝ) (n : ℕ) : ‖e θ ^ n‖ = 1 := by
  rw [norm_pow, norm_e, one_pow]

theorem e_ne_one {θ : ℝ} (h0 : θ ≠ 0) (h : |θ| ≤ π) : e θ ≠ 1 := by
  intro hc
  have hpos : 0 < 2 / π * |θ| := by
    have : 0 < |θ| := abs_pos.2 h0
    have := Real.pi_pos
    positivity
  have hle := mul_abs_le_norm_e_sub_one h
  rw [hc, sub_self, norm_zero] at hle
  linarith

end BlockCycleRotation

open BlockCycleRotation in
/-- **Observation 15, weighted sum, in the paper's sharp form.**
For `0 < |θ| ≤ π`,
`‖∑_{1 ≤ j < T} j · e(jθ)‖ ≤ π²/(2θ²) + (T-1)·π/(2|θ|)`. -/
theorem solution {θ : ℝ} (h0 : θ ≠ 0) (h : |θ| ≤ π) (T : ℕ) :
    ‖∑ j ∈ Finset.Ico 1 T, (j : ℂ) * e θ ^ j‖
      ≤ π ^ 2 / (2 * θ ^ 2) + (T - 1 : ℕ) * π / (2 * |θ|):= by
  have hpi := Real.pi_pos
  have hθpos : 0 < |θ| := abs_pos.2 h0
  have hθsq : 0 < θ ^ 2 := by positivity
  have hne : e θ ≠ 1 := e_ne_one h0 h
  have hx1 : e θ - 1 ≠ 0 := sub_ne_zero.2 hne
  have hu : 0 < ‖e θ - 1‖ := norm_pos_iff.2 hx1
  -- the chord bound `2|θ|/π ≤ ‖e θ - 1‖`, in the two forms we need
  have hchord : 2 / π * |θ| ≤ ‖e θ - 1‖ := mul_abs_le_norm_e_sub_one h
  have hinv : 1 / ‖e θ - 1‖ ≤ π / (2 * |θ|) := by
    rw [div_le_div_iff₀ hu (by positivity)]
    have : 2 / π * |θ| * π = 2 * |θ| := by field_simp
    nlinarith [mul_le_mul_of_nonneg_right hchord hpi.le]
  have hinvsq : 1 / ‖e θ - 1‖ ^ 2 ≤ π ^ 2 / (4 * θ ^ 2) := by
    have h1 : (1 / ‖e θ - 1‖) ^ 2 ≤ (π / (2 * |θ|)) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hinv 2
    have hsq : (2 * |θ|) ^ 2 = 4 * θ ^ 2 := by
      rw [mul_pow, sq_abs]; norm_num
    have h2 : (π / (2 * |θ|)) ^ 2 = π ^ 2 / (4 * θ ^ 2) := by
      rw [div_pow, hsq]
    rw [div_pow, h2] at h1
    simpa using h1
  rcases Nat.eq_zero_or_pos T with hT | hT
  · subst hT
    rw [show Finset.Ico 1 0 = (∅ : Finset ℕ) from Finset.Ico_eq_empty (by omega),
      Finset.sum_empty, norm_zero]
    have h2 : ((0 - 1 : ℕ) : ℝ) = 0 := by norm_num
    rw [h2, zero_mul, zero_div, add_zero]
    exact le_of_lt (div_pos (by positivity) (by linarith))
  rw [weighted_geom_sum_closed hne T hT]
  have hnum : ‖((T - 1 : ℕ) : ℂ) * e θ ^ T - (e θ ^ T - e θ) / (e θ - 1)‖
      ≤ (T - 1 : ℕ) + 2 / ‖e θ - 1‖ := by
    refine (norm_sub_le _ _).trans ?_
    have h1 : ‖((T - 1 : ℕ) : ℂ) * e θ ^ T‖ = (T - 1 : ℕ) := by
      rw [norm_mul, norm_e_pow, mul_one, Complex.norm_natCast]
    have h2 : ‖(e θ ^ T - e θ) / (e θ - 1)‖ ≤ 2 / ‖e θ - 1‖ := by
      rw [norm_div]
      gcongr
      calc ‖e θ ^ T - e θ‖ ≤ ‖e θ ^ T‖ + ‖e θ‖ := norm_sub_le _ _
        _ = 2 := by rw [norm_e_pow, norm_e]; norm_num
    linarith
  rw [norm_div]
  have hstep : ‖((T - 1 : ℕ) : ℂ) * e θ ^ T - (e θ ^ T - e θ) / (e θ - 1)‖ / ‖e θ - 1‖
      ≤ ((T - 1 : ℕ) + 2 / ‖e θ - 1‖) / ‖e θ - 1‖ := by
    gcongr
  refine hstep.trans ?_
  have hexp : ((T - 1 : ℕ) + 2 / ‖e θ - 1‖) / ‖e θ - 1‖
      = (T - 1 : ℕ) * (1 / ‖e θ - 1‖) + 2 * (1 / ‖e θ - 1‖ ^ 2) := by
    field_simp
  rw [hexp]
  have hA : ((T - 1 : ℕ) : ℝ) * (1 / ‖e θ - 1‖) ≤ ((T - 1 : ℕ) : ℝ) * (π / (2 * |θ|)) :=
    mul_le_mul_of_nonneg_left hinv (by positivity)
  have hB : 2 * (1 / ‖e θ - 1‖ ^ 2) ≤ 2 * (π ^ 2 / (4 * θ ^ 2)) :=
    mul_le_mul_of_nonneg_left hinvsq (by norm_num)
  have hBB : 2 * (π ^ 2 / (4 * θ ^ 2)) = π ^ 2 / (2 * θ ^ 2) := by
    rw [eq_div_iff (by positivity : (2 : ℝ) * θ ^ 2 ≠ 0)]
    field_simp
    ring
  have hAA : ((T - 1 : ℕ) : ℝ) * (π / (2 * |θ|)) = ((T - 1 : ℕ) : ℝ) * π / (2 * |θ|) := by
    ring
  linarith [hA, hB]
