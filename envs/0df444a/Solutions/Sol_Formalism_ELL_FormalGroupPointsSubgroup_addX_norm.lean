-- Prove2me | solution 1 for Formalism.ELL.FormalGroupPointsSubgroup.addX_norm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:23:11.312476+00:00
-- url     : https://prove2.me/submissions/49d714be-c36e-4b62-ab31-74b9b7517b6a

import Mathlib
import Definitions.Def_Formalism_EllipticTorsion_FormalGroupPointsTorsionFree
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_FormalGroupPointsSubgroupHolds
import Theorems.Thm_Formalism_ELL_FormalGroupPointsSubgroup_add_le
import Theorems.Thm_Formalism_ELL_FormalGroupPointsSubgroup_sub_le
import Theorems.Thm_Formalism_ELL_FormalGroupPointsSubgroup_le_sub_of_lt
import Theorems.Thm_Formalism_ELL_FormalGroupPointsSubgroup_mul_le
import Theorems.Thm_Formalism_ELL_FormalGroupPointsSubgroup_y_int
import Theorems.Thm_Formalism_ELL_FormalGroupPointsSubgroup_y_sq_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
universe u
open Formalism Formalism.ELL Formalism.ELL.FormalGroupPointsSubgroup
open WeierstrassCurve Polynomial
variable {K : Type u} [NormedField K] [IsUltrametricDist K]
namespace Formalism.ELL.FormalGroupPointsSubgroup
theorem _root_.solution [DecidableEq K] (W : WeierstrassCurve K) (hW : IntegralModel W)
    {x₁ x₂ y₁ y₂ : K} (h₁ : W.toAffine.Equation x₁ y₁) (h₂ : W.toAffine.Equation x₂ y₂)
    (hxy : ¬(x₁ = x₂ ∧ y₁ = W.toAffine.negY x₂ y₂)) (hx₁ : 1 < ‖x₁‖) (hx₂ : 1 < ‖x₂‖) :
    1 < ‖W.toAffine.addX x₁ x₂ (W.toAffine.slope x₁ x₂ y₁ y₂)‖ := by
  set ℓ := W.toAffine.slope x₁ x₂ y₁ y₂ with hℓ
  set x₃ := W.toAffine.addX x₁ x₂ ℓ with hx₃
  set y₃ := W.toAffine.negAddY x₁ x₂ y₁ ℓ with hy₃
  by_contra hC
  push Not at hC
  have h₃ : W.toAffine.Equation x₃ y₃ := Affine.equation_negAdd h₁ h₂ hxy
  have hy3 : ‖y₃‖ ≤ 1 := y_int W hW h₃ hC
  have hpoly := Affine.addPolynomial_slope h₁ h₂ hxy
  rw [← hℓ] at hpoly
  have hev := congrArg (Polynomial.eval (x₃ + 1)) hpoly
  simp only [Affine.addPolynomial, Affine.linePolynomial, Affine.polynomial] at hev
  simp at hev
  have hx3def : x₃ = ℓ ^ 2 + W.toAffine.a₁ * ℓ - W.toAffine.a₂ - x₁ - x₂ := by simp [hx₃]
  rw [← hx3def] at hev
  obtain ⟨a1, a2, a3, a4, a6⟩ := hW

  have hy3def : y₃ = ℓ * (x₃ - x₁) + y₁ := by simp [hy₃, hx₃]
  have hx0 : 0 ≤ ‖x₁‖ := norm_nonneg _
  have hℓ0 : 0 ≤ ‖ℓ‖ := norm_nonneg _
  have hsq := y_sq_le W ⟨a1, a2, a3, a4, a6⟩ h₁ hx₁
  have hd : ‖x₁‖ ≤ ‖x₁ - x₃‖ := le_sub_of_lt (by linarith)
  have hlin : ‖ℓ‖ * ‖x₁‖ ≤ max ‖y₁‖ 1 := by
    have e : ℓ * (x₁ - x₃) = y₁ - y₃ := by rw [hy3def]; ring
    have : ‖ℓ * (x₁ - x₃)‖ ≤ max ‖y₁‖ 1 := by
      rw [e]; exact sub_le (le_max_left _ _) (hy3.trans (le_max_right _ _))
    rw [norm_mul] at this
    nlinarith
  have hℓsq : ‖ℓ‖ ^ 2 ≤ ‖x₁‖ := by
    have hm : (max ‖y₁‖ 1) ^ 2 ≤ ‖x₁‖ ^ 3 := by
      rcases le_total ‖y₁‖ 1 with h | h
      · rw [max_eq_right h, one_pow]; exact one_le_pow₀ hx₁.le
      · rw [max_eq_left h]; exact hsq
    have : (‖ℓ‖ * ‖x₁‖) ^ 2 ≤ ‖x₁‖ ^ 3 :=
      (pow_le_pow_left₀ (by positivity) hlin 2).trans hm
    have hx1p : 0 < ‖x₁‖ ^ 2 := by positivity
    nlinarith

  set M := max 1 ‖ℓ‖ with hM
  have hM1 : 1 ≤ M := le_max_left _ _
  have hMℓ : ‖ℓ‖ ≤ M := le_max_right _ _
  have hMsq : M ^ 2 ≤ ‖x₁‖ := by
    rcases le_total 1 ‖ℓ‖ with h | h
    · rw [hM, max_eq_right h]; exact hℓsq
    · rw [hM, max_eq_left h]; nlinarith
  have ht : ‖x₃ + 1‖ ≤ 1 := add_le hC (by simp)
  have hu : ‖ℓ * (x₃ + 1 - x₁) + y₁‖ ≤ M := by
    have e : ℓ * (x₃ + 1 - x₁) + y₁ = y₃ + ℓ := by rw [hy3def]; ring
    rw [e]; exact add_le (hy3.trans hM1) hMℓ
  have hM2 : M ≤ M ^ 2 := by nlinarith
  have hLHS : ‖(ℓ * (x₃ + 1 - x₁) + y₁) ^ 2 + W.a₁ * (x₃ + 1) * (ℓ * (x₃ + 1 - x₁) + y₁)
      + W.a₃ * (ℓ * (x₃ + 1 - x₁) + y₁)
      - ((x₃ + 1) ^ 3 + W.a₂ * (x₃ + 1) ^ 2 + W.a₄ * (x₃ + 1) + W.a₆)‖ ≤ ‖x₁‖ := by
    have ht2 : ‖(x₃ + 1) ^ 2‖ ≤ 1 := by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) ht
    have ht3 : ‖(x₃ + 1) ^ 3‖ ≤ 1 := by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) ht
    have hc : ‖(x₃ + 1) ^ 3 + W.a₂ * (x₃ + 1) ^ 2 + W.a₄ * (x₃ + 1) + W.a₆‖ ≤ 1 := by
      refine add_le (add_le (add_le ht3 ?_) ?_) a6
      · simpa using mul_le a2 ht2
      · simpa using mul_le a4 ht
    refine sub_le (add_le (add_le ?_ ?_) ?_) (hc.trans (by nlinarith))
    · rw [norm_pow]; exact (pow_le_pow_left₀ (norm_nonneg _) hu 2).trans hMsq
    · have := mul_le (mul_le a1 ht) hu
      linarith
    · have := mul_le a3 hu
      linarith

  have hRHS : ‖x₁‖ * ‖x₂‖ ≤ ‖(x₃ + 1 - x₁) * (x₃ + 1 - x₂) * (x₃ + 1 - x₃)‖ := by
    have e1 : ‖x₁‖ ≤ ‖x₃ + 1 - x₁‖ := by
      rw [norm_sub_rev]; exact le_sub_of_lt (by linarith)
    have e2 : ‖x₂‖ ≤ ‖x₃ + 1 - x₂‖ := by
      rw [norm_sub_rev]; exact le_sub_of_lt (by linarith)
    have e3 : x₃ + 1 - x₃ = 1 := by ring
    rw [e3, mul_one, norm_mul]
    exact mul_le_mul e1 e2 (norm_nonneg _) (norm_nonneg _)
  have heq : (ℓ * (x₃ + 1 - x₁) + y₁) ^ 2 + W.a₁ * (x₃ + 1) * (ℓ * (x₃ + 1 - x₁) + y₁)
      + W.a₃ * (ℓ * (x₃ + 1 - x₁) + y₁)
      - ((x₃ + 1) ^ 3 + W.a₂ * (x₃ + 1) ^ 2 + W.a₄ * (x₃ + 1) + W.a₆) =
      -((x₃ + 1 - x₁) * (x₃ + 1 - x₂) * (x₃ + 1 - x₃)) := by
    linear_combination hev
  rw [heq, norm_neg] at hLHS
  have := hRHS.trans hLHS
  nlinarith
end Formalism.ELL.FormalGroupPointsSubgroup
