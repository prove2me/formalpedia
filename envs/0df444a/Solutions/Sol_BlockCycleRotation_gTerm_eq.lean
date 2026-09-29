-- Prove2me | solution 1 for BlockCycleRotation.gTerm_eq
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-05T11:35:46.668836+00:00
-- url     : https://prove2.me/submissions/5bf6708b-e547-41ca-9661-3d8e956cc063

import Definitions.Def_BlockCycleRotation_Continuant
import Definitions.Def_BlockCycleRotation_Euclid
import Definitions.Def_BlockCycleRotation_ExpSum
import Definitions.Def_BlockCycleRotation_Remark21
import Mathlib

open Real Finset Filter Topology

namespace BlockCycleRotation

@[simp]
theorem remSum_zero (n : ℕ) : remSum n 0 = 0 := by
  rw [remSum]; simp

@[simp]
theorem norm_e (θ : ℝ) : ‖e θ‖ = 1 := Complex.norm_exp_ofReal_mul_I θ

@[simp]
theorem norm_e_pow (θ : ℝ) (n : ℕ) : ‖e θ ^ n‖ = 1 := by
  rw [norm_pow, norm_e, one_pow]

@[simp]
theorem e_zero : e 0 = 1 := by simp [e]

@[simp] theorem K_nil : K [] = 1 := rfl

@[simp] theorem K_singleton (c : ℕ) : K [c] = c := rfl

@[simp] theorem cf_zero (a : ℕ) : cf a 0 = [] := by rw [cf]; simp

end BlockCycleRotation

open BlockCycleRotation in
/-- **Step 1 of Remark 21.**  `(2a+a')/(2a²(a+a')²) = (1/(2a'))(1/a² - 1/(a+a')²)`. -/
theorem solution (p : ℕ × ℕ) : gTerm p = (zTerm p - eTerm p) / 2:= by
  unfold gTerm zTerm eTerm
  split_ifs with h
  · obtain ⟨h1, h2⟩ := h
    have ha : (0 : ℝ) < (p.1 : ℝ) := by
      have : 0 < p.1 := by omega
      exact_mod_cast this
    have ha' : (0 : ℝ) < (p.2 : ℝ) := by
      have : 0 < p.2 := by omega
      exact_mod_cast this
    have haa : (0 : ℝ) < (p.1 : ℝ) + (p.2 : ℝ) := by linarith
    field_simp
    ring
  · norm_num
