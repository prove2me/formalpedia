-- Prove2me | solution 1 for BlockCycleRotation.exists_const_add_one_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-05T10:40:56.402203+00:00
-- url     : https://prove2.me/submissions/3e9fe9f5-1d19-4d4b-a941-759ee70d2ffc

import Definitions.Def_BlockCycleRotation_ExpSum
import Mathlib

open Real Finset

namespace BlockCycleRotation

@[simp]
theorem norm_e (θ : ℝ) : ‖e θ‖ = 1 := Complex.norm_exp_ofReal_mul_I θ

@[simp]
theorem norm_e_pow (θ : ℝ) (n : ℕ) : ‖e θ ^ n‖ = 1 := by
  rw [norm_pow, norm_e, one_pow]

@[simp]
theorem e_zero : e 0 = 1 := by simp [e]

/-- `1 ≤ (1 + s) ^ k` for `0 ≤ s`. -/
theorem one_le_one_add_pow {s : ℝ} (hs : 0 ≤ s) (k : ℕ) : (1 : ℝ) ≤ (1 + s) ^ k := by
  induction k with
  | zero => simp
  | succ n ih =>
    rw [pow_succ]
    nlinarith

/-- **Bernoulli's inequality**, proved here to keep this file self-contained. -/
theorem one_add_mul_le_one_add_pow {s : ℝ} (hs : 0 ≤ s) (k : ℕ) :
    1 + (k : ℝ) * s ≤ (1 + s) ^ k := by
  induction k with
  | zero => simp
  | succ n ih =>
    have h1 := one_le_one_add_pow hs n
    rw [pow_succ]
    push_cast
    nlinarith [mul_nonneg hs (sub_nonneg.2 h1)]

end BlockCycleRotation

open BlockCycleRotation in
/-- **`k + 1` is `O(t^k)` for any `t > 1`, with an explicit constant.**

Taking `s = t - 1`, Bernoulli gives `t^k ≥ 1 + k·s`, and `max 1 (2/s)` works:
for `k ≥ 1` we have `k + 1 ≤ 2k ≤ (2/s)·(k·s)`. -/
theorem solution {t : ℝ} (ht : 1 < t) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ k : ℕ, (k : ℝ) + 1 ≤ C * t ^ k:= by
  have hs0 : 0 < t - 1 := by linarith
  refine ⟨max 1 (2 / (t - 1)), le_max_left _ _, fun k => ?_⟩
  set s := t - 1 with hs
  set C := max 1 (2 / s) with hC
  have hC1 : (1 : ℝ) ≤ C := le_max_left _ _
  have hCge : 2 / s ≤ C := le_max_right _ _
  have hts : t = 1 + s := by rw [hs]; ring
  have hbern : 1 + (k : ℝ) * s ≤ t ^ k := by
    rw [hts]
    exact one_add_mul_le_one_add_pow hs0.le k
  have hstep : (k : ℝ) + 1 ≤ C * (1 + (k : ℝ) * s) := by
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk
      simpa using hC1
    · have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
      have hks : (0 : ℝ) ≤ (k : ℝ) * s := by positivity
      have hprod : 2 / s * ((k : ℝ) * s) ≤ C * ((k : ℝ) * s) :=
        mul_le_mul_of_nonneg_right hCge hks
      have heq : 2 / s * ((k : ℝ) * s) = 2 * (k : ℝ) := by field_simp
      have hexp : C * (1 + (k : ℝ) * s) = C + C * ((k : ℝ) * s) := by ring
      rw [hexp]
      linarith
  calc (k : ℝ) + 1 ≤ C * (1 + (k : ℝ) * s) := hstep
    _ ≤ C * t ^ k := mul_le_mul_of_nonneg_left hbern (by linarith)
