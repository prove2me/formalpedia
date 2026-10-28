-- Prove2me | solution 1 for D1Bound5.bennettTwoBetaFactor_le
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T01:30:24.388645+00:00
-- url     : https://prove2.me/submissions/3a2a0cab-bbaa-4ff8-b6cb-0164a2817311

import Lean.Elab.Tactic.Omega
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_BennettTwoBetaBound_Definitions
import Theorems.Thm_D1Bound5_bennettTwoBetaFactor_pos
import Theorems.Thm_D1Bound5_bennettTwoBetaFactor_succ
import Theorems.Thm_D1Bound5_bennettTwoBeta_ratio_lt_one

section
namespace D1Bound5









/-- Exact first value; both half-integer Gamma factors are evaluated. -/
theorem bennettTwoBetaFactor_one : bennettTwoBetaFactor 1 = 27 / 64 := by
  have h3 : Real.Gamma (3 / 2 : ℝ) = (1 / 2 : ℝ) * Real.sqrt Real.pi := by
    convert Real.Gamma_add_one (by norm_num : (1 / 2 : ℝ) ≠ 0) using 1 <;>
      norm_num [Real.Gamma_one_half_eq]
  have h5 : Real.Gamma (5 / 2 : ℝ) = (3 / 2 : ℝ) * Real.Gamma (3 / 2 : ℝ) := by
    convert Real.Gamma_add_one (by norm_num : (3 / 2 : ℝ) ≠ 0) using 1 <;> norm_num
  norm_num [bennettTwoBetaFactor, h3, h5] <;>
    field_simp [Real.pi_ne_zero] <;> nlinarith [Real.sq_sqrt Real.pi_pos.le]





theorem bennettTwoBetaFactor_succ_lt (k : ℕ) (hk : 1 ≤ k) :
    bennettTwoBetaFactor (k + 1) < bennettTwoBetaFactor k := by
  rw [bennettTwoBetaFactor_succ k hk]
  simpa only [mul_one] using
    mul_lt_mul_of_pos_left (bennettTwoBeta_ratio_lt_one k hk) (bennettTwoBetaFactor_pos k hk)

/-- Uniform quantitative bound on the exact normalized beta factor, for all orders. -/
theorem _root_.solution (k : ℕ) (hk : 1 ≤ k) :
    bennettTwoBetaFactor k ≤ 27 / 64 := by
  have h : ∀ n : ℕ, bennettTwoBetaFactor (n + 1) ≤ 27 / 64 := by
    intro n
    induction n with
    | zero => exact bennettTwoBetaFactor_one.le
    | succ n ih =>
        exact (bennettTwoBetaFactor_succ_lt (n + 1) (by omega)).le.trans ih
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  exact h n



end D1Bound5
end
