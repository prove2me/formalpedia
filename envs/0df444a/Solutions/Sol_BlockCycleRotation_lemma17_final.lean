-- Prove2me | solution 1 for BlockCycleRotation.lemma17_final
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-05T11:32:10.733763+00:00
-- url     : https://prove2.me/submissions/5185b271-bee7-44f8-84ea-1c3a568983c2

import Definitions.Def_BlockCycleRotation_Constant
import Definitions.Def_BlockCycleRotation_Continuant
import Definitions.Def_BlockCycleRotation_Euclid
import Definitions.Def_BlockCycleRotation_ExpSum
import Theorems.Thm_BlockCycleRotation_lemma17
import Theorems.Thm_BlockCycleRotation_lemma17_E
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
/-- **Lemma 17, with the error instantiated.** -/
theorem solution {n : ℕ} (hn : 0 < n) :
    |G1 n - cConst * (n : ℝ) ^ 2 * ∑ d ∈ n.divisors, 1 / (d : ℝ) ^ 2|
      ≤ ∑ d ∈ n.divisors, Eterm n d:=
  lemma17 hn (Eterm n) (fun d hd => lemma17_E hn d hd)
