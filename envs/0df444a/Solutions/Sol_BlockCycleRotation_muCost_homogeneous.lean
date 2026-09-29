-- Prove2me | solution 1 for BlockCycleRotation.muCost_homogeneous
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-05T12:12:17.961007+00:00
-- url     : https://prove2.me/submissions/40d7050e-2247-4f0e-b082-8e7f42842b56

import Definitions.Def_BlockCycleRotation_Algorithm
import Definitions.Def_BlockCycleRotation_Buffer
import Definitions.Def_BlockCycleRotation_Continuant
import Definitions.Def_BlockCycleRotation_Euclid
import Definitions.Def_BlockCycleRotation_ExpSum
import Mathlib

open Finset Filter Topology Real MeasureTheory BoxIntegral
open scoped ENNReal

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
theorem cost_zero (n : ℕ) : cost n 0 = 0 := by
  rw [cost]; simp

@[simp]
theorem finalSeg_zero (n : ℕ) : finalSeg n 0 = n := by
  rw [finalSeg]; simp

@[simp]
theorem e_zero : e 0 = 1 := by simp [e]

@[simp] theorem K_nil : K [] = 1 := rfl

@[simp] theorem K_singleton (c : ℕ) : K [c] = c := rfl

@[simp] theorem cf_zero (a : ℕ) : cf a 0 = [] := by rw [cf]; simp

@[simp]
theorem costB_zero (n b : ℕ) : costB n 0 b = 0 := by rw [costB]; simp

end BlockCycleRotation

open BlockCycleRotation in
/-- **Corollary, item 2: homogeneity.**  `μ(λN, λℓ, λβ) = λ·μ(N,ℓ,β)`. -/
theorem solution {lam N l b : ℝ} (hlam : 0 < lam) (hN : 0 < N) :
    muCost (lam * N) (lam * l) (lam * b) = lam * muCost N l b:= by
  unfold muCost
  have h1 : lam * b / (lam * N) = b / N := by
    rw [mul_div_mul_left _ _ (ne_of_gt hlam)]
  have h2 : lam * l / (lam * N) = l / N := by
    rw [mul_div_mul_left _ _ (ne_of_gt hlam)]
  rw [h1, h2]
  ring
