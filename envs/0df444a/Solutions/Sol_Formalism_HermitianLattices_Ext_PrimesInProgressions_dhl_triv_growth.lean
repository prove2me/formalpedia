-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.dhl_triv_growth
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:01:14.239914+00:00
-- url     : https://prove2.me/submissions/08994db8-46c7-4097-9574-a01787e70b29

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDHSt
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_ZetaGrowth
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDHLocalA
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_dhl_prod_le
import Theorems.Thm_Formalism_ZF_growthBound


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
theorem _root_.solution (M : ℕ) [NeZero M] (s : ℂ) (hs : 1 / 2 ≤ s.re) :
    ‖DirichletCharacter.LFunctionTrivChar₁ M s‖ ≤ 4 * M * (1 + ‖s‖) ^ 2 := by
  have hM : (1 : ℝ) ≤ M := by exact_mod_cast NeZero.one_le
  have hs0 := norm_nonneg s
  by_cases h1 : s = 1
  · subst h1
    have := dhl_prod_le M 1 (by simp)
    simp only [Function.update_self]
    have e : ∏ p ∈ M.primeFactors, (1 - (p : ℂ)⁻¹) = ∏ p ∈ M.primeFactors, (1 - (p : ℂ) ^ (-(1 : ℂ))) := by
      refine Finset.prod_congr rfl (fun p _ => ?_)
      rw [cpow_neg_one]
    rw [e]
    refine this.trans ?_
    rw [norm_one]
    nlinarith
  · rw [DirichletCharacter.LFunctionTrivChar₁, Function.update_of_ne h1,
      DirichletCharacter.LFunctionTrivChar_eq_mul_riemannZeta h1, norm_mul, norm_mul]
    have hP := dhl_prod_le M s (by linarith)
    have hz := Formalism.ZF.growthBound s (by linarith) h1
    have hpos : 0 < ‖s - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr h1)
    have hle : ‖s - 1‖ ≤ 1 + ‖s‖ := by
      have := norm_sub_le s 1; rw [norm_one] at this; linarith
    have hb : 1 / s.re ≤ 2 := by
      rw [div_le_iff₀ (by linarith)]; linarith
    have hz2 : ‖s - 1‖ * ‖riemannZeta s‖ ≤ 4 * (1 + ‖s‖) ^ 2 := by
      calc ‖s - 1‖ * ‖riemannZeta s‖
          ≤ ‖s - 1‖ * (1 + 1 / ‖s - 1‖ + ‖s‖ * (1 + 1 / s.re)) := by gcongr
        _ = ‖s - 1‖ + 1 + ‖s - 1‖ * (‖s‖ * (1 + 1 / s.re)) := by field_simp
        _ ≤ (1 + ‖s‖) + 1 + (1 + ‖s‖) * (‖s‖ * (1 + 2)) := by gcongr
        _ ≤ 4 * (1 + ‖s‖) ^ 2 := by nlinarith
    calc ‖s - 1‖ * (‖∏ p ∈ M.primeFactors, (1 - (p : ℂ) ^ (-s))‖ * ‖riemannZeta s‖)
        = ‖∏ p ∈ M.primeFactors, (1 - (p : ℂ) ^ (-s))‖ * (‖s - 1‖ * ‖riemannZeta s‖) := by ring
      _ ≤ M * (4 * (1 + ‖s‖) ^ 2) := by gcongr
      _ = 4 * M * (1 + ‖s‖) ^ 2 := by ring
end Formalism.HermitianLattices.Ext.PrimesInProgressions
