-- Prove2me | solution 1 for BlockCycleRotation.main_term_substitute
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-05T11:29:18.897294+00:00
-- url     : https://prove2.me/submissions/5a2ff968-b614-4f3a-bc2b-3635b0018198

import Definitions.Def_BlockCycleRotation_Constant
import Definitions.Def_BlockCycleRotation_Continuant
import Definitions.Def_BlockCycleRotation_Euclid
import Definitions.Def_BlockCycleRotation_ExpSum
import Mathlib

open Real Finset

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
/-- **The substitution.**  The main term at a coprime pair is
`d·m/(a+a') + m²·cTerm(a,a')`. -/
theorem solution {m d a a' : ℕ} (h1 : 1 ≤ a') (h2 : a' < a)
    (h3 : Nat.gcd a a' = 1) :
    (1 / (a : ℝ)) * ((((d * a : ℕ) : ℝ) + (m : ℝ) / (a : ℝ)) * ((m : ℝ) / ((a : ℝ) + (a' : ℝ)))
        + (-(a' : ℝ) / (a : ℝ)) * ((m : ℝ) / ((a : ℝ) + (a' : ℝ))) ^ 2 / 2)
      = (d : ℝ) * (m : ℝ) / ((a : ℝ) + (a' : ℝ)) + (m : ℝ) ^ 2 * cTerm (a, a'):= by
  have ha : (0 : ℝ) < (a : ℝ) := by
    have : 0 < a := by omega
    exact_mod_cast this
  have ha'0 : (0 : ℝ) ≤ (a' : ℝ) := by positivity
  have haa : (0 : ℝ) < (a : ℝ) + (a' : ℝ) := by linarith
  unfold cTerm
  rw [if_pos ⟨h1, h2, h3⟩]
  push_cast
  field_simp
  ring
