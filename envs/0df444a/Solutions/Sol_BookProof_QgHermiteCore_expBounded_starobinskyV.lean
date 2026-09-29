-- Prove2me | solution 1 for BookProof.QgHermiteCore.expBounded_starobinskyV
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T08:23:20.872349+00:00
-- url     : https://prove2.me/submissions/939956e1-2439-4b13-b348-6c98a1ce3b7e

import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
set_option autoImplicit false

theorem solution (M alpha : ℝ) (hM : 0 < M) :
    ∃ C c : ℝ, 0 ≤ c ∧ ∀ x : ℝ,
      |M ^ 4 / (16 * alpha) * (1 - Real.exp (-(Real.sqrt (2 / 3)) * x / M)) ^ 2| ≤
        C * Real.exp (c * ‖x‖) := by
  let k : ℝ := -(Real.sqrt (2 / 3)) / M
  refine ⟨|M ^ 4 / (16 * alpha)| * 4, 2 * |k|, by positivity, ?_⟩
  intro x
  have harg : -(Real.sqrt (2 / 3)) * x / M = k * x := by dsimp [k]; ring
  rw [harg, Real.norm_eq_abs, abs_mul, abs_pow]
  have he : Real.exp (k * x) ≤ Real.exp (|k| * |x|) :=
    Real.exp_le_exp.mpr (by simpa only [abs_mul] using le_abs_self (k * x))
  have hone : 1 ≤ Real.exp (|k| * |x|) := Real.one_le_exp (by positivity)
  have hb : |1 - Real.exp (k * x)| ≤ 2 * Real.exp (|k| * |x|) := by
    calc
      _ ≤ |(1 : ℝ)| + |Real.exp (k * x)| := by simpa only [sub_eq_add_neg, abs_neg] using abs_add_le (1 : ℝ) (-Real.exp (k * x))
      _ = 1 + Real.exp (k * x) := by simp [Real.exp_pos]
      _ ≤ _ := by linarith
  have hs := pow_le_pow_left₀ (abs_nonneg (1 - Real.exp (k * x))) hb 2
  have hexp : (2 * Real.exp (|k| * |x|)) ^ 2 = 4 * Real.exp ((2 * |k|) * |x|) := by
    rw [mul_pow, show (2 : ℝ) ^ 2 = 4 by norm_num, ← Real.exp_nat_mul]
    simp only [Nat.cast_ofNat, mul_assoc]
  rw [hexp] at hs
  calc
    _ ≤ |M ^ 4 / (16 * alpha)| * (4 * Real.exp ((2 * |k|) * |x|)) :=
      mul_le_mul_of_nonneg_left hs (abs_nonneg _)
    _ = _ := by ring
#print axioms solution
