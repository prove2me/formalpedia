-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.swap_rules
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T09:52:49.858803+00:00
-- url     : https://prove2.me/submissions/f7ab776a-82e2-4870-8a24-92eeb8edaa73

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FirstDeriv
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_ScalingSwapLemmas
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoVariableSwapLemmas_sw_zero
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoVariableSwapLemmas_sw_one
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoVariableSwapLemmas_coeff_swap2
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoVariableSwapLemmas_swap_two_sub
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoVariableSwapLemmas_swap_two_C_mul
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoVariableSwapLemmas_swap_two_single_mul
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoVariableSwapLemmas_swap_two_de_s

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.G7
open Formalism.DworkPowerSeriesWeights (Integral mvExp)
open TwoVariableSwapLemmas
namespace Formalism.InvariantFactorPaths.G7
theorem _root_.solution : SwapRules := by
  intro K _ _ p σ G γ γ' hp
  have hp0 : p ≠ 0 := by omega
  refine ⟨?_, ?_, ?_, ?_, swap_two_de_s hp0 σ G, ?_⟩
  · ext n
    have hsw : sw (sw n) = n := by
      ext i
      fin_cases i
      · exact (sw_zero _).trans (sw_one _)
      · exact (sw_one _).trans (sw_zero _)
    rw [coeff_swap2, coeff_swap2, hsw]
  · intro h n hn
    rw [coeff_swap2] at hn
    obtain ⟨h0, h1, h2⟩ := h _ hn
    rw [sw_zero, sw_one] at *
    refine ⟨h1, h0, ?_⟩
    have hsq : p * p ≡ 1 [MOD p ^ 2 - 1] := by
      have h1 : 1 ≤ p ^ 2 := Nat.one_le_pow _ _ (by omega)
      have : p * p = 1 + (p ^ 2 - 1) := by rw [← sq]; omega
      rw [this]
      simp [Nat.ModEq]
    calc n 0 = 1 * n 0 := (one_mul _).symm
      _ ≡ (p * p) * n 0 [MOD p ^ 2 - 1] := (hsq.symm).mul_right _
      _ = p * (p * n 0) := by ring
      _ ≡ p * n 1 [MOD p ^ 2 - 1] := (h2.symm).mul_left _
  · intro h n hn
    rw [coeff_swap2]
    apply h
    rw [sw_zero, sw_one]
    exact hn.symm
  · intro h n
    rw [coeff_swap2]
    exact h _
  · unfold Hser
    rw [swap_two_sub, swap_two_sub, swap_two_C_mul, swap_two_C_mul, swap_two_single_mul, swap_two_single_mul,
      swap_two_de_s hp0]
    ring
end Formalism.InvariantFactorPaths.G7
