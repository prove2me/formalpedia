-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.B4.progTwo
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:03:47.916876+00:00
-- url     : https://prove2.me/submissions/c18c08c8-766b-462e-a8d4-7b2f572402dc

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_ExceptionalCharacterBounds_EffFinal
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_LogEightBound_ProgTwo
import Theorems.Thm_Formalism_HermitianLattices_Ext_B4_log_eight_mul_le
import Theorems.Thm_Formalism_HermitianLattices_Ext_SupplyAP_supplyPrimesEff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.B4
namespace Formalism.HermitianLattices.Ext.B4
theorem _root_.solution : ∃ C : ℝ, 0 < C ∧ ∀ M : ℕ, 3 ≤ M → ∃ p p' : ℕ, p ≠ p' ∧ p.Prime ∧ p'.Prime ∧
    p ≡ 1 [MOD M] ∧ p' ≡ 1 [MOD M] ∧ Real.log p ≤ C * Real.log M ^ 2 ∧ Real.log p' ≤ C * Real.log M ^ 2 := by
  obtain ⟨C, hC, h⟩ := Formalism.HermitianLattices.Ext.SupplyAP.supplyPrimesEff
  refine ⟨9 * C, by positivity, fun M hM => ?_⟩
  obtain ⟨S, hS, hq⟩ := h M 2 (by omega)
  obtain ⟨p, p', hne, rfl⟩ := Finset.card_eq_two.1 hS
  have hMR : (3 : ℝ) ≤ M := by exact_mod_cast hM
  have hlog0 : 0 ≤ Real.log (2 * (M : ℝ) * ((2 : ℕ) + 2)) := by
    apply Real.log_nonneg; push_cast; nlinarith
  have hle := log_eight_mul_le hM
  have hsq : Real.log (2 * (M : ℝ) * ((2 : ℕ) + 2)) ^ 2 ≤ 9 * Real.log M ^ 2 := by nlinarith
  have key : ∀ q ∈ ({p, p'} : Finset ℕ), Real.log q ≤ 9 * C * Real.log M ^ 2 := by
    intro q hqS
    obtain ⟨hqp, -, hqle⟩ := hq q hqS
    have hq0 : (0 : ℝ) < q := by exact_mod_cast hqp.pos
    have h1 : Real.log q ≤ C * Real.log (2 * (M : ℝ) * ((2 : ℕ) + 2)) ^ 2 := by
      have := Real.log_le_log hq0 hqle
      rwa [Real.log_exp] at this
    nlinarith
  have hp := hq p (by simp)
  have hp' := hq p' (by simp)
  exact ⟨p, p', hne, hp.1, hp'.1, hp.2.1, hp'.2.1, key p (by simp), key p' (by simp)⟩
end Formalism.HermitianLattices.Ext.B4
