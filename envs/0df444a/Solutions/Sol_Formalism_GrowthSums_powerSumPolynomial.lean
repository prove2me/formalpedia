-- Prove2me | solution 1 for Formalism.GrowthSums.powerSumPolynomial
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:02:32.597525+00:00
-- url     : https://prove2.me/submissions/7adfc132-55cf-4b6e-8665-c7a011846fdb

import Definitions.Def_Formalism_GrowthSums_StatementA
import Definitions.Def_Formalism_GrowthSums_FactorialBaseGrowth_Harmonic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
open Finset
open Formalism Formalism.GrowthSums
namespace Formalism.GrowthSums
theorem _root_.solution : PowerSumPoly := by
  intro s
  classical
  have hcoeff : (Polynomial.bernoulli (s + 1)).coeff (s + 1) = 1 := by
    rw [Polynomial.bernoulli_def, Polynomial.finset_sum_coeff,
      Finset.sum_eq_single (s + 1)]
    · simp [Polynomial.coeff_monomial]
    · intro b _ hb
      rw [Polynomial.coeff_monomial, if_neg hb]
    · intro h
      exact absurd (Finset.self_mem_range_succ (s + 1)) h
  have hle : (Polynomial.bernoulli (s + 1)).natDegree ≤ s + 1 := by
    rw [Polynomial.bernoulli_def]
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro i hi
    exact (Polynomial.natDegree_monomial_le _).trans
      (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi))
  have hdeg : (Polynomial.bernoulli (s + 1)).natDegree = s + 1 :=
    Polynomial.natDegree_eq_of_le_of_coeff_ne_zero hle (by rw [hcoeff]; exact one_ne_zero)
  have hs : ((s : ℚ) + 1) ≠ 0 := by positivity
  refine ⟨Polynomial.C (1 / ((s : ℚ) + 1)) *
    (Polynomial.bernoulli (s + 1) - Polynomial.C (bernoulli (s + 1))), ?_, ?_⟩
  · rw [Polynomial.natDegree_C_mul (one_div_ne_zero hs), Polynomial.natDegree_sub_C, hdeg]
  · intro n
    have h := Polynomial.sum_range_pow_eq_bernoulli_sub n s
    simp only [Nat.succ_eq_add_one] at h
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_sub]
    rw [← h, ← mul_assoc, one_div_mul_cancel hs, one_mul]
end Formalism.GrowthSums
