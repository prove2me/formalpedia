-- Prove2me | solution 1 for ConsistentSubmodular.Objective.finiteExpectation_lipschitz
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:34:57.71491+00:00
-- url     : https://prove2.me/submissions/f5aaa736-fcaf-43cc-b0fc-33b94765e36a

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Reduction_SharedThreshold
import Theorems.Thm_ConsistentSubmodular_FiniteLaw_expect_pushforward
import Theorems.Thm_ConsistentSubmodular_FiniteLaw_product_selected_probability
import Theorems.Thm_ConsistentSubmodular_exists_sharedThreshold
import Theorems.Thm_ConsistentSubmodular_sharedThresholdSample_recourse_expectation

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

noncomputable section

open scoped BigOperators

namespace ConsistentSubmodular

variable {n d : ℕ}

theorem sharedThresholdSample_expectation {z : Fin d → Fin n → ℝ}
    (T : ∀ e, SharedThreshold (fun t => z t e)) (t : Fin d)
    (v : Finset (Fin n) → ℝ) :
    (FiniteLaw.product (fun e => (T e).law)).expect (fun ω => v (sharedThresholdSample T ω t)) =
      finiteExpectation (z t) v := by
  unfold sharedThresholdSample
  rw [FiniteLaw.product_selected_expectation]
  have hp : (fun e => (T e).law.probability (fun a => t ∈ (T e).active a)) = z t :=
    funext (fun e => (T e).inclusion t)
  rw [hp]

end ConsistentSubmodular

end

end

section

noncomputable section

open scoped BigOperators

namespace ConsistentSubmodular

namespace Objective

variable {n : ℕ} (f : Objective n)

theorem union_increment_le (V : ℝ)
    (hV : ∀ i, f.value {i} - f.value ∅ ≤ V) (S T : Finset (Fin n)) :
    f.value (S ∪ T) - f.value S ≤ V * T.card := by
  classical
  induction T using Finset.induction_on with
  | empty => simp
  | @insert e T he ih =>
    have h := f.diminishing_returns (Finset.empty_subset (S ∪ T)) {e}
    simp only [Finset.empty_union] at h
    have hu : S ∪ insert e T = (S ∪ T) ∪ {e} := by
      ext i
      simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
      tauto
    rw [hu, Finset.card_insert_of_notMem he, Nat.cast_add, Nat.cast_one]
    nlinarith [hV e]

theorem value_sub_le_recourse (V : ℝ) (hV0 : 0 ≤ V)
    (hV : ∀ i, f.value {i} - f.value ∅ ≤ V) (S T : Finset (Fin n)) :
    f.value S - f.value T ≤ V * recourse S T := by
  classical
  have h := f.union_increment_le V hV T (S \ T)
  have hm : f.value S ≤ f.value (T ∪ (S \ T)) := by
    apply f.monotone
    intro e he
    by_cases ht : e ∈ T
    · exact Finset.mem_union_left _ ht
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨he, ht⟩)
  have hc : ((S \ T).card : ℝ) ≤ (recourse S T : ℝ) := by
    exact_mod_cast Finset.card_le_card (Finset.subset_union_left :
      S \ T ⊆ (S \ T) ∪ (T \ S))
  have := mul_le_mul_of_nonneg_left hc hV0
  linarith

end Objective

end ConsistentSubmodular

end

end

section

open scoped BigOperators
open ConsistentSubmodular
open ConsistentSubmodular.Objective
variable {n : ℕ} (f : Objective n)

theorem solution (V : ℝ) (hV0 : 0 ≤ V)
    (hV : ∀ i, f.value {i} - f.value ∅ ≤ V)
    (p q : Fin n → ℝ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    (hq : ∀ i, 0 ≤ q i ∧ q i ≤ 1) :
    |finiteExpectation p f.value - finiteExpectation q f.value| ≤
      V * ∑ i, |p i - q i| := by
  classical
  let z : Fin 2 → Fin n → ℝ := fun t => if t = 0 then p else q
  have hz (i : Fin n) (t : Fin 2) : 0 ≤ z t i ∧ z t i ≤ 1 := by
    dsimp [z]
    split_ifs
    · exact hp i
    · exact hq i
  let T : ∀ i, SharedThreshold (fun t => z t i) := fun i =>
    Classical.choice (exists_sharedThreshold _ (hz i))
  let μ := FiniteLaw.product (fun i => (T i).law)
  let S := fun ω t => sharedThresholdSample T ω t
  have hd (s t : Fin 2) :
      finiteExpectation (z s) f.value - finiteExpectation (z t) f.value ≤
        V * ∑ i, |z s i - z t i| := by
    rw [← sharedThresholdSample_expectation T s f.value,
      ← sharedThresholdSample_expectation T t f.value,
      ← sharedThresholdSample_recourse_expectation T s t]
    change μ.expect (fun ω => f.value (S ω s)) -
      μ.expect (fun ω => f.value (S ω t)) ≤
      V * μ.expect (fun ω => (recourse (S ω s) (S ω t) : ℝ))
    unfold FiniteLaw.expect
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro ω _
    have h := mul_le_mul_of_nonneg_left
      (f.value_sub_le_recourse V hV0 hV (S ω s) (S ω t)) (μ.nonnegative ω)
    nlinarith
  apply abs_le.mpr
  constructor
  · have h := hd 1 0
    norm_num [z, abs_sub_comm] at h
    linarith
  · simpa [z] using hd 0 1

end
