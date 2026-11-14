-- Prove2me | solution 1 for ConsistentSubmodular.FiniteLaw.product_probability_all
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:29:33.361146+00:00
-- url     : https://prove2.me/submissions/5424661a-ea5d-4425-b4b1-25e138778614

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Reduction_FiniteProductLaw

section

open scoped BigOperators
open ConsistentSubmodular ConsistentSubmodular.FiniteLaw
variable {Ω : Type*} [Fintype Ω] (μ : FiniteLaw Ω)
variable {κ : Type*} [Fintype κ] [DecidableEq κ]
variable {A : κ → Type*} [∀ i, Fintype (A i)]

theorem solution (laws : ∀ i, FiniteLaw (A i))
    (E : ∀ i, A i → Prop) :
    (product laws).probability (fun ω => ∀ i, E i (ω i)) = ∏ i, (laws i).probability (E i) := by
  classical
  have hpoint (ω : ∀ i, A i) :
      (if ∀ i, E i (ω i) then ∏ i, (laws i).weight (ω i) else 0) =
        ∏ i, if E i (ω i) then (laws i).weight (ω i) else 0 := by
    by_cases h : ∀ i, E i (ω i)
    · simp [h]
    · rw [if_neg h]
      push Not at h
      obtain ⟨i, hi⟩ := h
      exact (Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])).symm
  unfold probability product
  simp only [hpoint]
  exact (Fintype.prod_sum (fun i (a : A i) => if E i a then (laws i).weight a else 0)).symm

end
