-- Prove2me | solution 1 for BalanceSpecification.FiniteEntropy.shannon_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:53:59.809418+00:00
-- url     : https://prove2.me/submissions/f6ebcf2b-0a10-4980-9e6d-82ffe8b05c8b

module
public import Definitions.Def_BalanceSpecificaton_FiniteEntropy
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_EntropyAlgebra

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification BalanceSpecification.FiniteEntropy
variable {ι : Type*} [Fintype ι]
namespace BalanceSpecification.FiniteEntropy
theorem _root_.solution {p : ι → ℝ} (hp : ∀ i, 0 ≤ p i)
    (hsum : ∑ i, p i = 1) : 0 ≤ shannon p := by
  apply Finset.sum_nonneg
  intro i _
  have hpone : p i ≤ 1 := by
    rw [← hsum]
    exact Finset.single_le_sum (fun j _ => hp j) (Finset.mem_univ i)
  exact mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr (hp i))
    (Real.log_nonpos (hp i) hpone)
end BalanceSpecification.FiniteEntropy
