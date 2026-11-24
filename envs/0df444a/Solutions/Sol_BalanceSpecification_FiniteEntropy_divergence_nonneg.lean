-- Prove2me | solution 1 for BalanceSpecification.FiniteEntropy.divergence_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:51:23.846324+00:00
-- url     : https://prove2.me/submissions/fc3f3fa7-488a-44fe-aa2c-2cf83ff56740

module
public import Definitions.Def_BalanceSpecificaton_FiniteEntropy
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_EntropyAlgebra
public import Theorems.Thm_BalanceSpecification_FiniteEntropy_sub_le_mul_log_div

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification BalanceSpecification.FiniteEntropy
variable {ι : Type*} [Fintype ι]
namespace BalanceSpecification.FiniteEntropy
theorem _root_.solution {p q : ι → ℝ} (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i)
    (hpsum : ∑ i, p i = 1) (hqsum : ∑ i, q i = 1)
    (hsupport : ∀ i, p i ≠ 0 → 0 < q i) : 0 ≤ divergence p q := by
  have hsum := Finset.sum_le_sum (s := Finset.univ)
    (fun i _ => sub_le_mul_log_div (hp i) (hq i) (hsupport i))
  simpa only [Finset.sum_sub_distrib, hpsum, hqsum, sub_self, divergence] using hsum
end BalanceSpecification.FiniteEntropy
