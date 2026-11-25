-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.exLF_growth
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:02:14.970807+00:00
-- url     : https://prove2.me/submissions/a03d6abc-208f-4c57-9605-135eb5a2079d

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTExplDefs
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTExplLF
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_exLF_of_ne
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_exLF_one_char
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_exLF_one_char_apply
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_exLF_prod_le
import Theorems.Thm_Formalism_ZF_growthBound
import Theorems.Thm_Formalism_ZeroFreeDirichlet_lfunction_polynomial_growth


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Classical
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimesInProgressions
open Formalism.ZeroFreeDirichlet
variable {M : ℕ} [NeZero M]
namespace Formalism.HermitianLattices.Ext.PrimesInProgressions
theorem _root_.solution : ∃ C : ℝ, 1 ≤ C ∧ ∀ (M : ℕ) [NeZero M] (χ : DirichletCharacter ℂ M) (s : ℂ), 1 / 2 ≤ s.re →
    ‖exLF χ s‖ ≤ C * M * (1 + ‖s‖) ^ 2 := by
  obtain ⟨C0, hC0⟩ := lfunction_polynomial_growth
  refine ⟨max C0 6, le_trans (by norm_num) (le_max_right _ _), ?_⟩
  intro M _ χ s hs
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast NeZero.one_le
  have hn : 0 ≤ ‖s‖ := norm_nonneg s
  by_cases h : χ = 1
  · subst h
    have h6 : 6 * (M : ℝ) * (1 + ‖s‖) ^ 2 ≤ max C0 6 * M * (1 + ‖s‖) ^ 2 := by
      gcongr; exact le_max_right _ _
    refine le_trans ?_ h6
    by_cases hs1 : s = 1
    · subst hs1
      rw [exLF_one_char]
      simp only [Function.update_self]
      have := exLF_prod_le M 1 (by norm_num)
      have he : ∏ p ∈ M.primeFactors, (1 - (p : ℂ) ^ (-(1 : ℂ))) = ∏ p ∈ M.primeFactors, (1 - (p : ℂ)⁻¹) := by
        refine Finset.prod_congr rfl (fun p _ => ?_)
        rw [Complex.cpow_neg_one]
      rw [he] at this
      refine this.trans ?_
      rw [norm_one]; nlinarith
    · rw [exLF_one_char_apply hs1]
      have hz := DirichletCharacter.LFunctionTrivChar_eq_mul_riemannZeta (N := M) hs1
      simp only [DirichletCharacter.LFunctionTrivChar] at hz
      rw [hz]
      have hP := exLF_prod_le M s hs
      have hZ := Formalism.ZF.growthBound s (by linarith) hs1
      have hpos : 0 < ‖s - 1‖ := norm_pos_iff.2 (sub_ne_zero_of_ne hs1)
      have hle : ‖s - 1‖ ≤ 1 + ‖s‖ := by
        calc ‖s - 1‖ ≤ ‖s‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
          _ = 1 + ‖s‖ := by rw [norm_one]; ring
      have hre : 1 / s.re ≤ 2 := by
        rw [div_le_iff₀ (by linarith)]; linarith
      have hA : ‖s - 1‖ * ‖riemannZeta s‖ ≤ 6 * (1 + ‖s‖) ^ 2 := by
        calc ‖s - 1‖ * ‖riemannZeta s‖ ≤ ‖s - 1‖ * (1 + 1 / ‖s - 1‖ + ‖s‖ * (1 + 1 / s.re)) := by gcongr
          _ = ‖s - 1‖ + 1 + ‖s - 1‖ * (‖s‖ * (1 + 1 / s.re)) := by field_simp
          _ ≤ (1 + ‖s‖) + 1 + (1 + ‖s‖) * (‖s‖ * (1 + 2)) := by gcongr
          _ ≤ 6 * (1 + ‖s‖) ^ 2 := by nlinarith
      calc ‖(s - 1) * ((∏ p ∈ M.primeFactors, (1 - (p : ℂ) ^ (-s))) * riemannZeta s)‖
          = ‖∏ p ∈ M.primeFactors, (1 - (p : ℂ) ^ (-s))‖ * (‖s - 1‖ * ‖riemannZeta s‖) := by
            rw [norm_mul, norm_mul]; ring
        _ ≤ M * (6 * (1 + ‖s‖) ^ 2) := by gcongr
        _ = 6 * (M : ℝ) * (1 + ‖s‖) ^ 2 := by ring
  · rw [exLF_of_ne h]
    have h1 := hC0 M χ h s hs
    have h2 : C0 * M * (1 + ‖s‖) ≤ max C0 6 * M * (1 + ‖s‖) := by
      gcongr; exact le_max_left _ _
    have h3 : max C0 6 * M * (1 + ‖s‖) ≤ max C0 6 * M * (1 + ‖s‖) ^ 2 := by
      have hc : 0 ≤ max C0 6 * M := by
        have : (0 : ℝ) ≤ max C0 6 := le_trans (by norm_num) (le_max_right _ _)
        positivity
      have : (1 + ‖s‖) ≤ (1 + ‖s‖) ^ 2 := by nlinarith
      exact mul_le_mul_of_nonneg_left this hc
    linarith
end Formalism.HermitianLattices.Ext.PrimesInProgressions
