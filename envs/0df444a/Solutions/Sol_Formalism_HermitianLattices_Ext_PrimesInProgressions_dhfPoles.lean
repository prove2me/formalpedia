-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.dhfPoles
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:02:09.927999+00:00
-- url     : https://prove2.me/submissions/79ef5b61-2868-475f-aeb0-67a6fb3b2aab

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDHIneqB
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDHIneqFA
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_dhfShiftPoleN
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Finset Complex Classical
noncomputable section
namespace Formalism.HermitianLattices.Ext.PrimesInProgressions
private theorem one_eighth_le_abs_of_not_mem_pole_disc (γ β₁ : ℝ) (hβ1 : 19 / 20 ≤ β₁) (hβ2 : β₁ < 1)
    (h : ¬ ‖(β₁ : ℂ) - ((26 / 25 : ℂ) + γ * I)‖ ≤ 4 / 25) : 1 / 8 ≤ |γ| := by
  by_contra hlt
  push_neg at hlt
  apply h
  have hg : γ ^ 2 < 1 / 64 := by
    have := abs_lt.mp hlt
    nlinarith
  rw [← sq_le_sq₀ (norm_nonneg _) (by norm_num), Complex.sq_norm, Complex.normSq_apply]
  simp
  nlinarith
end Formalism.HermitianLattices.Ext.PrimesInProgressions
end
end

set_option autoImplicit false
open Finset Complex Classical
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimesInProgressions
namespace Formalism.HermitianLattices.Ext.PrimesInProgressions
theorem _root_.solution {M : ℕ} (χ₁ χ : DirichletCharacter ℂ M) (hχ₁2 : χ₁ ^ 2 = 1) (hχ₁1 : χ₁ ≠ 1)
    (η γ β₁ : ℝ) (hη : 0 < η) (hβ1 : 19 / 20 ≤ β₁) (hβ2 : β₁ < 1) (k : ℕ) (s : ℂ)
    (hs : s = ((1 + η : ℝ) : ℂ) + γ * I) [Decidable (χ = 1)] [Decidable (χ * χ₁ = 1)]
    (c3 c4 : Prop) [Decidable c3] [Decidable c4]
    (h3 : χ = χ₁ → ¬ c3 → ¬ ‖(β₁ : ℂ) - ((26 / 25 : ℂ) + γ * I)‖ ≤ 4 / 25)
    (h4 : χ = 1 → ¬ c4 → ¬ ‖(β₁ : ℂ) - ((26 / 25 : ℂ) + γ * I)‖ ≤ 4 / 25)
    (h3' : c3 → χ = χ₁) (h4' : c4 → χ = 1) :
    ‖(if χ = 1 then 1 / (s - 1) ^ (k + 1) else 0) + (if χ * χ₁ = 1 then 1 / (s - 1) ^ (k + 1) else 0)
      - (if c3 then 1 / (s - β₁) ^ (k + 1) else 0) - (if c4 then 1 / (s - β₁) ^ (k + 1) else 0)‖
      ≤ ((k : ℝ) + 1) * (1 - β₁) / η ^ (k + 2) + 8 ^ (k + 1) := by
  have hpos : 0 ≤ ((k : ℝ) + 1) * (1 - β₁) / η ^ (k + 2) + 8 ^ (k + 1) := by
    have : 0 ≤ ((k : ℝ) + 1) * (1 - β₁) / η ^ (k + 2) := by
      apply div_nonneg
      · apply mul_nonneg
        · positivity
        · linarith
      · positivity
    exact add_nonneg this (by positivity)
  by_cases h1 : χ = 1
  · have h2 : ¬ (χ * χ₁ = 1) := by
      rw [h1, one_mul]
      exact hχ₁1
    have h3n : ¬ c3 := fun h => hχ₁1 ((h3' h).symm.trans h1)
    simp only [if_pos h1, if_neg h2, if_neg h3n, add_zero, sub_zero]
    exact dhfShiftPoleN η γ β₁ hη hβ2 k c4 (fun h => one_eighth_le_abs_of_not_mem_pole_disc γ β₁ hβ1 hβ2 (h4 h1 h)) s hs
  · by_cases h2 : χ * χ₁ = 1
    · have hχ : χ = χ₁ := by
        have e : χ = χ * χ₁ * χ₁ := by rw [mul_assoc, ← sq, hχ₁2, mul_one]
        rw [e, h2, one_mul]
      have h4n : ¬ c4 := fun h => h1 (h4' h)
      simp only [if_neg h1, if_pos h2, if_neg h4n, zero_add, sub_zero]
      exact dhfShiftPoleN η γ β₁ hη hβ2 k c3 (fun h => one_eighth_le_abs_of_not_mem_pole_disc γ β₁ hβ1 hβ2 (h3 hχ h)) s hs
    · have h3n : ¬ c3 := fun h => h2 (by rw [h3' h, ← sq, hχ₁2])
      have h4n : ¬ c4 := fun h => h1 (h4' h)
      simp only [if_neg h1, if_neg h2, if_neg h3n, if_neg h4n, add_zero, sub_zero, norm_zero]
      exact hpos
end Formalism.HermitianLattices.Ext.PrimesInProgressions
