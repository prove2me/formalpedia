-- Prove2me | solution 1 for BlockCycleRotation.cost_le_muCost
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-05T12:13:34.484455+00:00
-- url     : https://prove2.me/submissions/71d71977-16bb-4f71-bc58-c1ebb65f9782

import Definitions.Def_BlockCycleRotation_Algorithm
import Definitions.Def_BlockCycleRotation_Average
import Definitions.Def_BlockCycleRotation_Buffer
import Definitions.Def_BlockCycleRotation_Continuant
import Definitions.Def_BlockCycleRotation_Euclid
import Definitions.Def_BlockCycleRotation_ExpSum
import Definitions.Def_BlockCycleRotation_Theorem10
import Theorems.Thm_BlockCycleRotation_relation
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
/-- **Corollary, item 3, unbuffered case.**  The actual move count is at most
`μ(N,ℓ,0⁺) = N·f(ℓ/N)`; this is equation (relation). -/
theorem solution {n k : ℕ} (hn : 0 < n) (hk : k ≤ n) :
    ((algCost n k : ℕ) : ℝ) ≤ (n : ℝ) * fCost ((k : ℝ) / (n : ℝ)):= by
  have h := relation hn hk
  have hg : (0 : ℝ) ≤ ((Nat.gcd n k : ℕ) : ℝ) := by positivity
  linarith
