-- Prove2me | solution 1 for ConsistentSubmodular.Objective.exists_residual_rounding
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:39:36.476026+00:00
-- url     : https://prove2.me/submissions/e503e3b9-9dc0-4175-b2fb-b32897eb7900

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Reduction_SamplingScale
import Theorems.Thm_ConsistentSubmodular_sampleExpectation_inter_zero
import Theorems.Thm_ConsistentSubmodular_Objective_exists_forced_set
import Theorems.Thm_ConsistentSubmodular_Objective_contractOn_singleton_cap
import Theorems.Thm_ConsistentSubmodular_Objective_contractOn_expectation_le
import Theorems.Thm_ConsistentSubmodular_exists_finite_joint_rounding

section

noncomputable section

open scoped BigOperators

namespace ConsistentSubmodular

variable {ι : Type*} [DecidableEq ι]

theorem sampleExpectation_univ [Fintype ι] (p : ι → ℝ) (v : Finset ι → ℝ) :
    sampleExpectation Finset.univ p v = finiteExpectation p v := by
  simp [sampleExpectation, finiteExpectation, subsetWeight, bernoulliWeight,
    Finset.compl_eq_univ_sdiff]

theorem sampleExpectation_congr (U : Finset ι) (p : ι → ℝ) {v w : Finset ι → ℝ}
    (h : ∀ S ⊆ U, v S = w S) : sampleExpectation U p v = sampleExpectation U p w := by
  exact Finset.sum_congr rfl (fun S hS => by rw [h S (Finset.mem_powerset.mp hS)])

theorem sampleExpectation_sub (U : Finset ι) (p : ι → ℝ) (v w : Finset ι → ℝ) :
    sampleExpectation U p (fun S => v S - w S) = sampleExpectation U p v - sampleExpectation U p w := by
  simp only [sampleExpectation, mul_sub, Finset.sum_sub_distrib]

end ConsistentSubmodular

end

end

section

noncomputable section

open scoped BigOperators

namespace ConsistentSubmodular.Objective

variable {n : ℕ} (f : Objective n)

theorem contractOn_expectation_eq (U B : Finset (Fin n)) (p : Fin n → ℝ)
    (hp : ∀ e ∉ U, p e = 0) :
    finiteExpectation p (f.contractOn U B).value =
      finiteExpectation p (fun S => f.value (B ∪ S)) - f.value B := by
  rw [← sampleExpectation_univ, ← sampleExpectation_univ]
  rw [sampleExpectation_inter_zero U Finset.univ p hp,
    sampleExpectation_inter_zero U Finset.univ p hp, Finset.univ_inter]
  have he : sampleExpectation U p (f.contractOn U B).value =
      sampleExpectation U p (fun S => f.value (B ∪ S) - f.value B) := by
    apply sampleExpectation_congr
    intro S hS
    simp [contractOn, Finset.inter_eq_left.mpr hS]
  rw [he, sampleExpectation_sub, sampleExpectation_const]

theorem contractOn_expectation_add_forced_lower (U D Q : Finset (Fin n)) (p : Fin n → ℝ)
    (hp : ∀ e, 0 ≤ p e ∧ p e ≤ 1) (hsupport : ∀ e ∉ U, p e = 0) :
    finiteExpectation p (fun S => f.value (Q ∪ S)) - f.value (D ∪ Q) ≤
      finiteExpectation p (f.contractOn U (D ∪ Q)).value := by
  rw [f.contractOn_expectation_eq U (D ∪ Q) p hsupport]
  apply sub_le_sub_right
  exact finiteExpectation_mono p hp (fun S => f.monotone _ _
    (Finset.union_subset_union_left Finset.subset_union_right))

end ConsistentSubmodular.Objective

end

end

section

open scoped BigOperators
open ConsistentSubmodular ConsistentSubmodular.Objective
variable {n : ℕ} (f : Objective n)

theorem solution {τ ι ε : Type*} [Fintype τ] [Fintype ι] [Fintype ε]
    (U : Finset (Fin n)) (κ H : ℕ) (hH : 0 < H) (hHκ : H ≤ κ)
    (V : ℝ) (hV : 0 < V) (hscale : ∀ A ⊆ U, A.card ≤ κ → f.value A ≤ V)
    (z : τ → Fin n → ℝ) (hz : ∀ t e, 0 ≤ z t e ∧ z t e ≤ 1)
    (hsupport : ∀ t e, e ∉ U → z t e = 0) (hsize : ∀ t, ∑ e, z t e ≤ κ)
    (Q : ι → Finset (Fin n)) (left right : ι → τ) (edgeLeft edgeRight : ε → τ)
    (target : ι → ℝ)
    (htarget : ∀ i, target i ≤ finiteExpectation
      (fun e => min (z (left i) e) (z (right i) e)) (fun S => f.value (Q i ∪ S)))
    (a b R pSize pValue pCost : ℝ) (ha : 0 ≤ a) (hb : 0 < b) (hb2 : b ≤ 2 * κ) (hR : 0 < R)
    (hsizeBudget : Real.exp (-(b ^ 2) / (4 * κ)) ≤ pSize)
    (hvalueBudget : Real.exp (-(a ^ 2) / (2 * (V / H) * (2 * V))) ≤ pValue)
    (hcostBudget : (∑ j, ∑ e, |z (edgeLeft j) e - z (edgeRight j) e|) ≤ R * pCost)
    (hbudget : (Fintype.card τ : ℝ) * pSize + (Fintype.card ι : ℝ) * pValue + pCost < 1) :
    ∃ D : Finset (Fin n), ∃ S : τ → Finset (Fin n), D ⊆ U ∧ D.card < H ∧
      (∀ t, S t ⊆ U) ∧
      (∀ t e, z t e = 0 → e ∉ S t) ∧
      (∀ t e, z t e = 1 → e ∈ S t) ∧
      (∀ t, (S t).card ≤ (κ : ℝ) + b) ∧
      (∀ i, target i - a ≤ f.value (Q i ∪ (D ∪ (S (left i) ∩ S (right i))))) ∧
      (∑ j, (recourse (S (edgeLeft j)) (S (edgeRight j)) : ℝ)) < R ∧
      (∀ s t, (∀ e, z s e = z t e) → S s = S t) := by
  classical
  have hHr : (0 : ℝ) < H := Nat.cast_pos.mpr hH
  have hκ : 0 < κ := lt_of_lt_of_le hH hHκ
  have hpay : V ≤ (H : ℝ) * (V / H) := by rw [mul_div_cancel₀ _ (ne_of_gt hHr)]
  obtain ⟨D, hDU, hDH, hcap⟩ := f.exists_forced_set U κ H hH hHκ (V / H) V hscale hpay
  have hmincube (i : ι) (e) :
      0 ≤ min (z (left i) e) (z (right i) e) ∧ min (z (left i) e) (z (right i) e) ≤ 1 :=
    ⟨le_min (hz _ e).1 (hz _ e).1, (min_le_left _ _).trans (hz _ e).2⟩
  have hminmass (i : ι) : (∑ e, min (z (left i) e) (z (right i) e)) ≤ κ :=
    (Finset.sum_le_sum (fun e _ => min_le_left _ _)).trans (hsize (left i))
  have hminsupport (i : ι) (e) (he : e ∉ U) : min (z (left i) e) (z (right i) e) = 0 := by
    simp [hsupport _ e he]
  obtain ⟨S, hzero, hone, hcard, hval, hcost, hequal⟩ := exists_finite_joint_rounding z hz
    (fun i => f.contractOn U (D ∪ Q i)) left right edgeLeft edgeRight
    κ (V / H) (2 * V) a b R pSize pValue pCost ha hb hb2 hR (div_pos hV hHr) (by positivity)
    hsize (fun i => f.contractOn_singleton_cap U D (Q i) (div_nonneg hV.le hHr.le) hcap)
    (fun i => f.contractOn_expectation_le U (D ∪ Q i) κ hκ hV.le hscale _ (hmincube i) (hminmass i))
    hsizeBudget hvalueBudget hcostBudget hbudget
  have hSU (t) : S t ⊆ U := by
    intro e he
    by_contra heU
    exact hzero t e (hsupport t e heU) he
  refine ⟨D, S, hDU, hDH, hSU, hzero, hone, hcard, ?_, hcost, hequal⟩
  intro i
  have hlift := f.contractOn_expectation_add_forced_lower U D (Q i) _
    (hmincube i) (hminsupport i)
  have h := hval i
  have hint : (S (left i) ∩ S (right i)) ∩ U = S (left i) ∩ S (right i) :=
    Finset.inter_eq_left.mpr (Finset.inter_subset_left.trans (hSU (left i)))
  change _ ≤ f.value ((D ∪ Q i) ∪ ((S (left i) ∩ S (right i)) ∩ U)) - f.value (D ∪ Q i) at h
  rw [hint] at h
  have hunion : (D ∪ Q i) ∪ (S (left i) ∩ S (right i)) =
      Q i ∪ (D ∪ (S (left i) ∩ S (right i))) := by ext e; simp; tauto
  rw [hunion] at h
  linarith [htarget i]

end
