-- Prove2me | solution 2 for BalanceSpecification.FiniteEntropy.sum_mul_shannon_le
-- status  : ACCEPTED   (prove)
-- author  : @grencez
-- created : 2026-11-24T03:13:45.186838+00:00
-- url     : https://prove2.me/submissions/833c7c1f-512e-4acc-a3ac-931a32676008

import Mathlib
import Definitions.Def_BalanceSpecificaton_FiniteEntropy
open BalanceSpecification.FiniteEntropy
variable {ι κ : Type*} [Fintype ι] [Fintype κ]


theorem solution {w : κ → ℝ} (hw : ∀ k, 0 ≤ w k) (hw1 : ∑ k, w k = 1)
    {p : κ → ι → ℝ} (hp : ∀ k i, 0 ≤ p k i) :
    ∑ k, w k * shannon (p k) ≤ shannon (fun i => ∑ k, w k * p k i) := by
  unfold shannon
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum; intro i hi
  simpa [smul_eq_mul, Real.negMulLog_def] using Real.concaveOn_negMulLog.le_map_sum (t := Finset.univ) (p := fun k => p k i) (fun k _ => hw k) hw1 (fun k _ => hp k i)
