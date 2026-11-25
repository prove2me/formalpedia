-- Prove2me | solution 1 for ErdosGirth.two_mul_pow_le_exp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:31:13.924421+00:00
-- url     : https://prove2.me/submissions/1bc4a32f-7d9a-4ea4-b075-4ec8b3a836c0

module
public import Mathlib
public import Definitions.Def_GirthLib_ErdosGirthAux

set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph
open ErdosGirth
namespace ErdosGirth
theorem _root_.solution (a q : ℕ) (hq : 6 * 2 ^ (a + 3) * (a + 3).factorial ≤ q) :
    2 * ((q : ℝ) + 1) ^ (a + 2) ≤ Real.exp (((q : ℝ) - 1) / 2) := by
  obtain ⟨y, hy⟩ : ∃ y : ℝ, y = ((q : ℝ) + 1) / 2 := ⟨_, rfl⟩
  have hF : (0 : ℝ) < (a + 3).factorial := by exact_mod_cast Nat.factorial_pos _
  have hqR : (6 * 2 ^ (a + 3) * (a + 3).factorial : ℝ) ≤ q := by exact_mod_cast hq
  have hy0 : 0 < y := by rw [hy]; positivity
  have hyb : 3 * 2 ^ (a + 3) * ((a + 3).factorial : ℝ) ≤ y := by rw [hy]; linarith
  have he : Real.exp 1 ≤ 3 := le_of_lt (lt_trans Real.exp_one_lt_d9 (by norm_num))
  have hexp : y ^ (a + 3) / (a + 3).factorial ≤ Real.exp y :=
    Real.pow_div_factorial_le_exp y hy0.le (a + 3)
  have hsplit : Real.exp y = Real.exp 1 * Real.exp (((q : ℝ) - 1) / 2) := by
    rw [← Real.exp_add, hy]; congr 1; ring
  have hq1 : (q : ℝ) + 1 = 2 * y := by rw [hy]; ring
  rw [hq1]
  have hE0 : 0 < Real.exp (((q : ℝ) - 1) / 2) := Real.exp_pos _
  -- 2 (2y)^(a+2) * e * (a+3)! ≤ y^(a+3) ≤ (a+3)! e^y
  have key : 2 * (2 * y) ^ (a + 2) * 3 * (a + 3).factorial ≤ y ^ (a + 3) := by
    have : 2 * (2 * y) ^ (a + 2) * 3 * (a + 3).factorial
        = (3 * 2 ^ (a + 3) * (a + 3).factorial) * y ^ (a + 2) := by ring
    have h3 : y ^ (a + 3) = y * y ^ (a + 2) := by ring
    rw [this, h3]
    exact mul_le_mul_of_nonneg_right hyb (pow_nonneg hy0.le (a + 2))
  rw [div_le_iff₀ hF, hsplit] at hexp
  have h2 : 2 * (2 * y) ^ (a + 2) * Real.exp 1 * (a + 3).factorial
      ≤ 2 * (2 * y) ^ (a + 2) * 3 * (a + 3).factorial := by gcongr
  have := h2.trans (key.trans hexp)
  have hpos : 0 < Real.exp 1 * (a + 3).factorial := by positivity
  nlinarith
end ErdosGirth
