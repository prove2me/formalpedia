-- Prove2me | solution 1 for ConsistentSubmodular.FiniteLaw.product_selected_probability
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:31:06.791579+00:00
-- url     : https://prove2.me/submissions/9bee6cf9-55fa-4fdc-a55b-8911bb90fb1c

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Reduction_FiniteProductLaw
import Theorems.Thm_ConsistentSubmodular_FiniteLaw_product_probability_all

section

noncomputable section

open scoped BigOperators

namespace ConsistentSubmodular.FiniteLaw

variable {Ω : Type*} [Fintype Ω] (μ : FiniteLaw Ω)

theorem probability_not (E : Ω → Prop) : μ.probability (fun ω => ¬E ω) = 1 - μ.probability E := by
  classical
  unfold probability
  rw [← μ.sum_one, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro ω _
  by_cases h : E ω <;> simp [h]

end ConsistentSubmodular.FiniteLaw

end

end

section

open scoped BigOperators
open ConsistentSubmodular ConsistentSubmodular.FiniteLaw
variable {Ω : Type*} [Fintype Ω] (μ : FiniteLaw Ω)
variable {κ : Type*} [Fintype κ] [DecidableEq κ]
variable {A : κ → Type*} [∀ i, Fintype (A i)]

theorem solution (laws : ∀ i, FiniteLaw (A i))
    (select : ∀ i, A i → Prop) (S : Finset κ) :
    (product laws).probability (fun ω => selectedSet select ω = S) =
      bernoulliWeight (fun i => (laws i).probability (select i)) S := by
  classical
  have heq : (fun ω => selectedSet select ω = S) =
      (fun ω => ∀ i, if i ∈ S then select i (ω i) else ¬select i (ω i)) := by
    funext ω
    apply propext
    constructor
    · intro h i
      have hm := Finset.ext_iff.mp h i
      simp only [selectedSet, Finset.mem_filter, Finset.mem_univ, true_and] at hm
      by_cases hi : i ∈ S <;> simp [hi, hm]
    · intro h
      ext i
      have hi := h i
      simp only [selectedSet, Finset.mem_filter, Finset.mem_univ, true_and]
      by_cases hiS : i ∈ S <;> simpa [hiS] using hi
  rw [heq, product_probability_all laws (fun i a => if i ∈ S then select i a else ¬select i a)]
  have hpoint (i : κ) : (laws i).probability (fun a => if i ∈ S then select i a else ¬select i a) =
      if i ∈ S then (laws i).probability (select i) else 1 - (laws i).probability (select i) := by
    by_cases hi : i ∈ S <;> simp only [hi, ite_true, ite_false, probability_not]
  simp_rw [hpoint]
  unfold bernoulliWeight
  rw [Finset.prod_ite]
  congr 1 <;> congr 1 <;> ext i <;> simp

end
