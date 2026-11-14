-- Prove2me | solution 1 for ConsistentSubmodular.sharedThresholdSample_recourse_expectation
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:32:50.353065+00:00
-- url     : https://prove2.me/submissions/8f7ef71e-617e-4c57-b286-1a0eb311b9c7

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Reduction_SharedThreshold
import Theorems.Thm_ConsistentSubmodular_FiniteLaw_expect_pushforward
import Theorems.Thm_ConsistentSubmodular_FiniteLaw_product_selected_probability
import Theorems.Thm_ConsistentSubmodular_SharedThreshold_change_probability
import Theorems.Thm_ConsistentSubmodular_finiteExpectation_card

section

noncomputable section

open scoped BigOperators

namespace ConsistentSubmodular.FiniteLaw

variable {Ω : Type*} [Fintype Ω] (μ : FiniteLaw Ω)

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

variable {A : κ → Type*} [∀ i, Fintype (A i)]

/-- Any independent finite coordinate laws reproduce the Bernoulli law of
their coordinatewise inclusion events. -/
theorem product_selected_expectation (laws : ∀ i, FiniteLaw (A i))
    (select : ∀ i, A i → Prop) (v : Finset κ → ℝ) :
    (product laws).expect (fun ω => v (selectedSet select ω)) =
      finiteExpectation (fun i => (laws i).probability (select i)) v := by
  rw [expect_pushforward]
  simp only [product_selected_probability, finiteExpectation]

end ConsistentSubmodular.FiniteLaw

end

end

section

open scoped BigOperators
open ConsistentSubmodular
variable {n d : ℕ}

theorem solution {z : Fin d → Fin n → ℝ}
    (T : ∀ e, SharedThreshold (fun t => z t e)) (s t : Fin d) :
    (FiniteLaw.product (fun e => (T e).law)).expect
      (fun ω => (recourse (sharedThresholdSample T ω s) (sharedThresholdSample T ω t) : ℝ)) =
      ∑ e, |z s e - z t e| := by
  let changed := fun (e : Fin n) (a : Fin (T e).cellCount) =>
    (s ∈ (T e).active a ∧ t ∉ (T e).active a) ∨ (t ∈ (T e).active a ∧ s ∉ (T e).active a)
  have hchange (ω : ∀ e, Fin (T e).cellCount) :
      recourse (sharedThresholdSample T ω s) (sharedThresholdSample T ω t) =
        (FiniteLaw.selectedSet changed ω).card := by
    unfold recourse
    congr 1
    ext e
    simp only [sharedThresholdSample, FiniteLaw.selectedSet, Finset.mem_union, Finset.mem_sdiff,
      Finset.mem_filter, Finset.mem_univ, true_and, changed]
  simp_rw [hchange]
  rw [FiniteLaw.product_selected_expectation (fun e => (T e).law) changed
    (fun S => (S.card : ℝ)), finiteExpectation_card]
  apply Finset.sum_congr rfl
  intro e _
  exact (T e).change_probability s t

end
