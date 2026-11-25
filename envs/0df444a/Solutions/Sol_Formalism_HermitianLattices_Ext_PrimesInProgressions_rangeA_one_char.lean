-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.rangeA_one_char
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:45:50.315091+00:00
-- url     : https://prove2.me/submissions/02958399-fa91-417e-ba51-8be1aa89686b

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTEOf
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTRangeA
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_rangeA_far_term
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_rangeA_excZeros_empty
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_rangeA_excZeros_single
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_eOf_exc


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Complex Classical
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimesInProgressions
open Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds Formalism.ZeroFreeDirichlet
namespace Formalism.HermitianLattices.Ext.PrimesInProgressions
theorem _root_.solution (c C cA : ℝ)
    (H : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (B : Finset ℝ) (x : ℝ), ExcZeros cZ χ B → 2 ≤ x →
      (q : ℝ) ≤ Real.exp (c * Real.sqrt (Real.log x)) →
      ‖psiChi χ x - (if χ = 1 then (x : ℂ) else 0) + ∑ β ∈ B, (x : ℂ) ^ (β : ℂ) / (β : ℂ)‖ ≤
        C * x * Real.exp (-c * Real.sqrt (Real.log x)))
    (hcA : cA ≤ cZ) (hcA' : cA ≤ c) (M : ℕ) [NeZero M] (hM : 8 ≤ M) (y : ℝ) (hy : 2 ≤ y)
    (hl : Real.log M ≤ cA * Real.sqrt (Real.log y)) (χ : DirichletCharacter ℂ M) :
    ‖psiChi χ y - mainPsi (eOf M) χ y‖ ≤
      C * y * Real.exp (-c * Real.sqrt (Real.log y)) + 2 * y * Real.exp (-(Real.sqrt (Real.log y) / 2)) := by
  have hM2 : 2 ≤ M := by omega
  have hMr : (8 : ℝ) ≤ M := by exact_mod_cast hM
  have hs0 : 0 ≤ Real.sqrt (Real.log y) := Real.sqrt_nonneg _
  have hq : (M : ℝ) ≤ Real.exp (c * Real.sqrt (Real.log y)) := by
    rw [← Real.exp_log (by linarith : (0 : ℝ) < M)]
    exact Real.exp_le_exp.mpr (hl.trans (mul_le_mul_of_nonneg_right hcA' hs0))
  have hE : 0 ≤ 2 * y * Real.exp (-(Real.sqrt (Real.log y) / 2)) := by positivity
  have H' : ∀ B : Finset ℝ, ExcZeros cZ χ B →
      ‖psiChi χ y - mainPsi none χ y + ∑ β ∈ B, (y : ℂ) ^ (β : ℂ) / (β : ℂ)‖ ≤
        C * y * Real.exp (-c * Real.sqrt (Real.log y)) := by
    intro B hB
    have h0 := H M χ B y hB hy hq
    simp only [mainPsi, sub_zero]
    convert h0
  have hsome : ∀ (χ₁ : DirichletCharacter ℂ M) (β₁ : ℝ), mainPsi (some (χ₁, β₁)) χ y =
      mainPsi none χ y - (if χ = χ₁ then (y : ℂ) ^ (β₁ : ℂ) / (β₁ : ℂ) else 0) := by
    intro χ₁ β₁
    simp only [mainPsi, sub_zero]
    congr
  rcases he : eOf M with _ | ⟨χ₁, β₁⟩
  · have h0 := H' ∅ (rangeA_excZeros_empty M hM2 χ (by intro β hβ; rw [he] at hβ; simp at hβ))
    simp only [Finset.sum_empty, add_zero] at h0
    linarith
  · rw [hsome]
    by_cases hχ : χ = χ₁
    · subst hχ
      rw [if_pos rfl, ← sub_add]
      by_cases hr : InRegion cZ M (β₁ : ℂ)
      · have h0 := H' {β₁} (rangeA_excZeros_single M hM2 χ β₁ he hr)
        simp only [Finset.sum_singleton] at h0
        linarith
      · have h0 := H' ∅ (rangeA_excZeros_empty M hM2 χ (by
          intro β hβ; rw [he] at hβ
          have : β₁ = β := by simpa using hβ
          rw [← this]; exact hr))
        simp only [Finset.sum_empty, add_zero] at h0
        have hex := eOf_exc M _ he
        have hβ : 1 / 2 ≤ β₁ := by
          have h1 := hex.2.2.2.1
          have hlog : 1 ≤ Real.log M := by
            rw [Real.le_log_iff_exp_le (by linarith)]
            have := Real.exp_one_lt_d9
            linarith
          have : 1 / (8 * Real.log M) ≤ 1 / 8 := by
            apply one_div_le_one_div_of_le (by norm_num) (by linarith)
          simp only at h1
          linarith
        have h1 := rangeA_far_term M hM y cA β₁ hy hcA hl hβ hr
        exact (norm_add_le _ _).trans (add_le_add h0 h1)
    · have h0 := H' ∅ (rangeA_excZeros_empty M hM2 χ (by
          intro β hβ; rw [he] at hβ
          have : χ₁ = χ := by
            have := Option.some.inj hβ
            exact (Prod.mk.inj this).1
          exact absurd this.symm hχ))
      simp only [Finset.sum_empty, add_zero] at h0
      rw [if_neg hχ, sub_zero]
      linarith
end Formalism.HermitianLattices.Ext.PrimesInProgressions
