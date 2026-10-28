-- Prove2me | solution 2 for ComplementFreeCA.ValueQuery.value_query_mechanism
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T10:04:19.698679+00:00
-- url     : https://prove2.me/submissions/a85ac6d9-971d-4c80-881d-14e16879452a

import Mathlib
import Definitions.Def_ComplementFreeCA_ValueQuery_Basic
import Theorems.Thm_ComplementFreeCA_ValueQuery_alg_maximal_in_range
import Theorems.Thm_ComplementFreeCA_ValueQuery_case_one_all_to_one
import Theorems.Thm_ComplementFreeCA_ValueQuery_case_two_one_item_each
import Theorems.Thm_ComplementFreeCA_ValueQuery_maximal_in_range_incentive_compatible

-- carved verbatim out of submission 2e476c19-8f4f-47f2-8a0c-c07b537696cb, lines 231-259

section
open Finset ComplementFreeCA.ValueQuery

theorem solution {n m : ℕ}
    (mat : (Fin n → Finset (Fin m) → ℝ) → Fin m → Option (Fin n))
    (top : (Fin n → Finset (Fin m) → ℝ) → Fin n)
    (hmat : IsMaxWeightMatchingRule mat) (htop : IsTopBidderRule top) :
    (∀ v : Fin n → Finset (Fin m) → ℝ, (∀ i, IsCFValuation (v i)) →
      ∀ O : Fin n → Finset (Fin m), IsAllocation O →
        welfare v O ≤ 2 * Real.sqrt m * welfare v (alg mat top v)) ∧
    IncentiveCompatibleOn IsCFValuation (alg mat top) := by
  classical
  have hmax := ComplementFreeCA.ValueQuery.alg_maximal_in_range mat top hmat htop
  constructor
  · intro v hv O hO
    have hvnorm : ∀ i, IsNormalized (v i) := fun i => (hv i).1
    have hscale : 0 ≤ 2 * Real.sqrt m := by positivity
    by_cases hc : (∑ i ∈ univ.filter (fun i => ((O i).card : ℝ) < Real.sqrt m), v i (O i)) ≤
        ∑ i ∈ univ.filter (fun i => Real.sqrt m ≤ ((O i).card : ℝ)), v i (O i)
    · have hcase := ComplementFreeCA.ValueQuery.case_one_all_to_one v hv O hO hc (top v) (htop v)
      have hm := (hmax v hvnorm).2 (allToOne (top v)) (Or.inl ⟨top v, rfl⟩)
      have he : welfare v (allToOne (top v)) = v (top v) univ := by
        simp [welfare, allToOne, apply_ite, show ∀ i, v i ∅ = 0 from hvnorm]
      rw [he] at hm
      exact hcase.trans (mul_le_mul_of_nonneg_left hm hscale)
    · obtain ⟨A,hA,hcard,hval⟩ := ComplementFreeCA.ValueQuery.case_two_one_item_each v hv O hO (lt_of_not_ge hc)
      have hm := (hmax v hvnorm).2 A (Or.inr ⟨hA,hcard⟩)
      exact hval.trans (mul_le_mul_of_nonneg_left hm hscale)
  · apply ComplementFreeCA.ValueQuery.maximal_in_range_incentive_compatible IsCFValuation ValueQueryRange (alg mat top)
    intro v hv
    exact hmax v (fun i => (hv i).1)

end
