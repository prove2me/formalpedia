-- Prove2me | solution 1 for BalanceSpecification.FiniteEntropy.divergence_le_log_of_gibbs_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:17:18.964021+00:00
-- url     : https://prove2.me/submissions/e7922542-e2ab-4058-be91-36d3ea5dfaec

module
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_FiniteEntropy
public import Theorems.Thm_BalanceSpecification_FiniteEntropy_divergence_eq_neg_shannon_sub

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification BalanceSpecification.FiniteEntropy
variable {ι : Type*} [Fintype ι]
namespace BalanceSpecification.FiniteEntropy
theorem _root_.solution {p q : ι → ℝ} {K t : ℝ}
    (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) (hK : 0 < K)
    (hq : ∀ i, Real.exp (-t) / K ≤ q i) (hentropy : t ≤ shannon p) :
    divergence p q ≤ Real.log K := by
  have hpos i : 0 < q i := (div_pos (Real.exp_pos _) hK).trans_le (hq i)
  have hlog i : -t - Real.log K ≤ Real.log (q i) := by
    calc
      -t - Real.log K = Real.log (Real.exp (-t) / K) := by
        rw [Real.log_div (Real.exp_pos _).ne' hK.ne', Real.log_exp]
      _ ≤ Real.log (q i) := Real.log_le_log (div_pos (Real.exp_pos _) hK) (hq i)
  have hcross : -t - Real.log K ≤ ∑ i, p i * Real.log (q i) := by
    calc
      -t - Real.log K = (∑ i, p i) * (-t - Real.log K) := by rw [hsum, one_mul]
      _ = ∑ i, p i * (-t - Real.log K) := Finset.sum_mul _ _ _
      _ ≤ ∑ i, p i * Real.log (q i) :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hlog i) (hp i)
  rw [divergence_eq_neg_shannon_sub hpos]
  linarith only [hentropy, hcross]
end BalanceSpecification.FiniteEntropy
