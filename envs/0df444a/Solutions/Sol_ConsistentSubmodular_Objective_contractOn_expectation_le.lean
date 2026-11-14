-- Prove2me | solution 1 for ConsistentSubmodular.Objective.contractOn_expectation_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:33:18.174136+00:00
-- url     : https://prove2.me/submissions/28b5ec26-b80c-4d80-92ea-dddc4ba782d7

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Reduction_SamplingScale
import Theorems.Thm_ConsistentSubmodular_finiteExpectation_card
import Theorems.Thm_ConsistentSubmodular_Objective_exists_thinned_subset

section

noncomputable section

open scoped BigOperators

namespace ConsistentSubmodular

variable {n : ℕ}

namespace Objective

variable (f : Objective n)

theorem subadditive (A B : Finset (Fin n)) :
    f.value (A ∪ B) ≤ f.value A + f.value B := by
  have h := f.union_le A B
  have h0 := f.nonnegative ∅
  linarith

end Objective

end ConsistentSubmodular

end

end

section

noncomputable section

open scoped BigOperators

namespace ConsistentSubmodular

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem finiteExpectation_add (p : ι → ℝ) (v w : Finset ι → ℝ) :
    finiteExpectation p (fun S => v S + w S) = finiteExpectation p v + finiteExpectation p w := by
  simp only [finiteExpectation, mul_add, Finset.sum_add_distrib]

theorem finiteExpectation_mul (p : ι → ℝ) (c : ℝ) (v : Finset ι → ℝ) :
    finiteExpectation p (fun S => c * v S) = c * finiteExpectation p v := by
  simp only [finiteExpectation, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S _
  ring

end ConsistentSubmodular

end

end

section

noncomputable section

open scoped BigOperators

namespace ConsistentSubmodular.Objective

variable {n : ℕ} (f : Objective n)

theorem contractOn_le (U B S : Finset (Fin n)) :
    (f.contractOn U B).value S ≤ f.value (S ∩ U) := by
  have h := f.subadditive B (S ∩ U)
  change f.value (B ∪ (S ∩ U)) - f.value B ≤ f.value (S ∩ U)
  linarith

/-- A cardinality-constrained optimum bounds every larger set after thinning.
This loose affine bound is convenient under an arbitrary product law. -/
theorem cardinality_scale_bound (U : Finset (Fin n)) (k : ℕ) {V : ℝ}
    (hV : 0 ≤ V) (hscale : ∀ A ⊆ U, A.card ≤ k → f.value A ≤ V)
    (S : Finset (Fin n)) (hSU : S ⊆ U) :
    (k : ℝ) * f.value S ≤ ((k : ℝ) + S.card) * V := by
  by_cases hk : S.card ≤ k
  · have h := mul_le_mul_of_nonneg_left (hscale S hSU hk) (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
    have hcard := mul_nonneg (Nat.cast_nonneg S.card : (0 : ℝ) ≤ S.card) hV
    nlinarith
  · obtain ⟨A, hAS, hAk, hthin⟩ := f.exists_thinned_subset S k (by omega)
    have hA := hscale A (hAS.trans hSU) (by omega)
    have h := hthin.trans (mul_le_mul_of_nonneg_left hA (Nat.cast_nonneg S.card))
    have hkV := mul_nonneg (Nat.cast_nonneg k : (0 : ℝ) ≤ k) hV
    nlinarith

end ConsistentSubmodular.Objective

end

end

section

open scoped BigOperators
open ConsistentSubmodular ConsistentSubmodular.Objective
variable {n : ℕ} (f : Objective n)

theorem solution (U B : Finset (Fin n)) (k : ℕ) (hk : 0 < k)
    {V : ℝ} (hV : 0 ≤ V)
    (hscale : ∀ A ⊆ U, A.card ≤ k → f.value A ≤ V)
    (p : Fin n → ℝ) (hp : ∀ e, 0 ≤ p e ∧ p e ≤ 1)
    (hmass : ∑ e, p e ≤ k) :
    finiteExpectation p (f.contractOn U B).value ≤ 2 * V := by
  have hpoint (S : Finset (Fin n)) :
      (k : ℝ) * (f.contractOn U B).value S ≤ (k : ℝ) * V + V * S.card := by
    have hcontract := mul_le_mul_of_nonneg_left (f.contractOn_le U B S) (Nat.cast_nonneg k)
    have hscaleS := f.cardinality_scale_bound U k hV hscale (S ∩ U) Finset.inter_subset_right
    have hcard : ((S ∩ U).card : ℝ) ≤ S.card := Nat.cast_le.mpr (Finset.card_le_card Finset.inter_subset_left)
    have hprod := mul_le_mul_of_nonneg_right hcard hV
    nlinarith
  have he := finiteExpectation_mono p hp hpoint
  rw [finiteExpectation_mul, finiteExpectation_add, finiteExpectation_const,
    finiteExpectation_mul, finiteExpectation_card] at he
  have hm := mul_le_mul_of_nonneg_left hmass hV
  have hkreal : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  nlinarith

end
