-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.deuring_heilbronn_dominant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:46:46.025693+00:00
-- url     : https://prove2.me/submissions/d17c7223-15dc-4584-8a0b-e7934ee11643

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_DHFinish2Of
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDHPos
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDHDom
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_dhDom_hasSum
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_dhDom_term_le

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
open LSeries ArithmeticFunction DirichletCharacter
open scoped LSeries.notation
namespace Formalism.HermitianLattices.Ext.PrimesInProgressions
theorem _root_.solution : DHDom := by
  intro M _ χ₁ χ γ σ k h1 hσ
  have hs : 1 < ((σ : ℂ) + γ * I).re := by simpa using hσ
  have hs0 : 1 < (σ : ℂ).re := by simpa using hσ
  have hA := dhDom_hasSum χ k hs
  have hB := dhDom_hasSum (χ * χ₁) k hs
  have hC := dhDom_hasSum (1 : DirichletCharacter ℂ M) k hs0
  have hD := dhDom_hasSum χ₁ k hs0
  have hbound := HasSum.norm_le_of_bounded (hA.add hB) (Complex.hasSum_re (hC.add hD))
    (fun n ↦ by
      rw [Complex.add_re]
      exact dhDom_term_le χ₁ χ h1 k σ γ n)
  have e1 : ‖iteratedDeriv k (negLD χ) ((σ : ℂ) + γ * I)
      + iteratedDeriv k (negLD (χ * χ₁)) ((σ : ℂ) + γ * I)‖ =
      ‖(-1 : ℂ) ^ k * iteratedDeriv k (negLD χ) ((σ : ℂ) + γ * I)
        + (-1 : ℂ) ^ k * iteratedDeriv k (negLD (χ * χ₁)) ((σ : ℂ) + γ * I)‖ := by
    rw [← mul_add, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
  rw [e1, mul_add]
  exact hbound
end Formalism.HermitianLattices.Ext.PrimesInProgressions
