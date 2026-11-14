-- Prove2me | solution 1 for ConsistentSubmodular.sampleExpectation_lower_tail_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:33:44.347138+00:00
-- url     : https://prove2.me/submissions/d8c4102f-0a2a-4701-95a5-9d462afb7102

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Basic_SamplingOperators
import Theorems.Thm_ConsistentSubmodular_exp_neg_le_quadratic
import Theorems.Thm_ConsistentSubmodular_sampleExpectation_exp_neg_le

section

noncomputable section

open scoped BigOperators

namespace ConsistentSubmodular

variable {ι : Type*} [DecidableEq ι]

theorem sampleExpectation_mul (U : Finset ι) (p : ι → ℝ) (c : ℝ) (v : Finset ι → ℝ) :
    sampleExpectation U p (fun S => c * v S) = c * sampleExpectation U p v := by
  simp only [sampleExpectation, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S _
  ring

end ConsistentSubmodular

end

end

section

noncomputable section

open scoped BigOperators

namespace ConsistentSubmodular

variable {ι : Type*} [DecidableEq ι]

theorem const_le_sampleExpectation (U : Finset ι) (p : ι → ℝ)
    (hp : ∀ i ∈ U, 0 ≤ p i ∧ p i ≤ 1) {v : Finset ι → ℝ} {c : ℝ}
    (hv : ∀ S ⊆ U, c ≤ v S) : c ≤ sampleExpectation U p v := by
  have h := sampleExpectation_mono U p hp (v := fun _ => c) (w := v) hv
  rwa [sampleExpectation_const] at h

end ConsistentSubmodular

end

end

section

open scoped BigOperators
open ConsistentSubmodular
variable {ι : Type*} [DecidableEq ι]

theorem solution (U : Finset ι) (p : ι → ℝ)
    (hp : ∀ i ∈ U, 0 ≤ p i ∧ p i ≤ 1) (G : Finset ι → ℝ)
    (hmono : ∀ A B, A ⊆ B → G A ≤ G B)
    (hsub : ∀ A B, G (A ∪ B) + G (A ∩ B) ≤ G A + G B)
    {c M a : ℝ} (hc : 0 < c) (hcap : ∀ A e, G (insert e A) - G A ≤ c) (hM : 0 < M)
    (hmean : sampleExpectation U p G - G ∅ ≤ M) (ha : 0 ≤ a) :
    sampleExpectation U p (fun S => if G S ≤ sampleExpectation U p G - a then 1 else 0) ≤
      Real.exp (-(a ^ 2) / (2 * c * M)) := by
  set μ := sampleExpectation U p G with hμ
  let G' : Finset ι → ℝ := fun S => G S / c
  have h'mono : ∀ A B, A ⊆ B → G' A ≤ G' B :=
    fun A B h => div_le_div_of_nonneg_right (hmono A B h) hc.le
  have h'sub : ∀ A B, G' (A ∪ B) + G' (A ∩ B) ≤ G' A + G' B := by
    intro A B
    simp only [G', ← add_div]
    exact div_le_div_of_nonneg_right (hsub A B) hc.le
  have h'cap : ∀ A e, G' (insert e A) - G' A ≤ 1 := by
    intro A e
    simp only [G', ← sub_div]
    exact (div_le_one hc).mpr (hcap A e)
  set lam := a / M with hlamdef
  have hlam : 0 ≤ lam := div_nonneg ha hM.le
  have hmgf := sampleExpectation_exp_neg_le U p hp G' h'mono h'sub h'cap lam
  have hmean' : sampleExpectation U p G' = μ / c := by
    have h := sampleExpectation_mul U p (1 / c) G
    simp only [G', div_eq_mul_inv, one_mul] at h ⊢
    rw [mul_comm] at h
    rw [show (fun S => G S * c⁻¹) = (fun S => c⁻¹ * G S) from funext (fun S => mul_comm _ _), h,
      mul_comm]
  have hpoint : ∀ S ⊆ U, (if G S ≤ μ - a then (1 : ℝ) else 0) ≤
      Real.exp (lam * (μ - a) / c) * Real.exp (-lam * G' S) := by
    intro S _
    rw [← Real.exp_add]
    split_ifs with h
    · apply Real.one_le_exp_iff.mpr
      have hdiff : 0 ≤ (μ - a - G S) / c := div_nonneg (by linarith) hc.le
      have he : lam * (μ - a) / c + -lam * G' S = lam * ((μ - a - G S) / c) := by
        simp only [G']; ring
      rw [he]
      exact mul_nonneg hlam hdiff
    · exact (Real.exp_pos _).le
  have hP := sampleExpectation_mono U p hp hpoint
  rw [sampleExpectation_mul] at hP
  have hbound := hP.trans (mul_le_mul_of_nonneg_left hmgf (Real.exp_pos _).le)
  rw [← Real.exp_add, hmean'] at hbound
  refine hbound.trans (Real.exp_le_exp.mpr ?_)
  -- The exponent is at most `-a² / (2 c M)`.
  have hm0 : 0 ≤ (μ - G ∅) / c := by
    have h := const_le_sampleExpectation U p hp (v := G) (c := G ∅)
      (fun S _ => hmono _ _ (Finset.empty_subset S))
    exact div_nonneg (by rw [hμ]; linarith) hc.le
  have hmM : (μ - G ∅) / c ≤ M / c := div_le_div_of_nonneg_right hmean hc.le
  have hq0 : 0 ≤ lam + Real.exp (-lam) - 1 := by linarith [Real.one_sub_le_exp_neg lam]
  have hq1 : lam + Real.exp (-lam) - 1 ≤ lam ^ 2 / 2 := by
    linarith [exp_neg_le_quadratic hlam]
  have hprod : (μ - G ∅) / c * (lam + Real.exp (-lam) - 1) ≤ M / c * (lam ^ 2 / 2) :=
    mul_le_mul hmM hq1 hq0 (div_nonneg hM.le hc.le)
  have hexp : lam * (μ - a) / c + (-lam * G' ∅ + (μ / c - G' ∅) * (Real.exp (-lam) - 1)) =
      -(lam * a / c) + (μ - G ∅) / c * (lam + Real.exp (-lam) - 1) := by
    simp only [G']; ring
  rw [hexp]
  have hfinal : -(lam * a / c) + M / c * (lam ^ 2 / 2) = -(a ^ 2) / (2 * c * M) := by
    rw [hlamdef]
    field_simp
    ring
  linarith

end
