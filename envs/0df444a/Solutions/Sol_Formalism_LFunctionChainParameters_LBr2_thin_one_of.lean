-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LBr2.thin_one_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T02:10:22.148456+00:00
-- url     : https://prove2.me/submissions/a16b2a6c-d5a5-47cb-b7d5-00426c885aa9

import Definitions.Def_Formalism_SizeWindowBrackets_SmoothedRemainderRealIntegralFormula
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_GaloisMapComplexConjugation
import Definitions.Def_Formalism_LandauZeroFreeBounds_SiegelWalfiszAPOfSiegelLower
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_PrimeCongruenceConditions
import Theorems.Thm_Formalism_LFunctionChainParameters_LBr2_g_zeta_eq_g_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Filter Topology ArithmeticFunction DirichletCharacter
noncomputable section
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.LBr2
open Formalism Formalism.D5 Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LHost Formalism.LFunctionChainParameters.LErr Formalism.LFunctionChainParameters.LChain
  Formalism.LFunctionChainParameters.LChain2
namespace Formalism.LFunctionChainParameters.LBr2
theorem _root_.solution : ThinOneOf := by
  rintro ⟨c, K, hc, hK⟩ ε c' hε
  have T1 : Tendsto (fun x : ℝ => x ^ (ε / 8)) atTop atTop := tendsto_rpow_atTop (by positivity)
  have T2 : Tendsto (fun x : ℝ => c / 2 * x ^ (ε / 24) - c') atTop atTop :=
    tendsto_atTop_add_const_right _ _ ((tendsto_rpow_atTop (by positivity : 0 < ε / 24)).const_mul_atTop (by positivity))
  have T3 : Tendsto (fun x : ℝ => Real.exp (x ^ (ε / 8) * (c / 2 * x ^ (ε / 24) - c'))) atTop atTop :=
    Real.tendsto_exp_atTop.comp (T1.atTop_mul_atTop₀ T2)
  have E1 : ∀ᶠ x : ℝ in atTop, 1 ≤ x := eventually_ge_atTop 1
  have E2 : ∀ᶠ x : ℝ in atTop, 5 ≤ x ^ (ε / 3) := (tendsto_rpow_atTop (by positivity : 0 < ε / 3)).eventually_ge_atTop 5
  have E3 := T3.eventually_ge_atTop (max K 0)
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.1 (E1.and (E2.and E3))
  refine ⟨x₀, fun x hx y hy => ?_⟩
  obtain ⟨h1, h2, h3⟩ := hx₀ x hx
  have hx0 : 0 < x := by linarith
  set X := x ^ (ε / 3) with hX
  have hexp : X + 1 ≤ Real.exp X := Real.add_one_le_exp X
  have hy2 : 2 ≤ y := by linarith
  have hy0 : 0 < y := by linarith
  have hlog3 : Real.log 3 ≤ 2 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
    linarith
  have hlogy : X / 4 ≤ Real.log y := by
    have h4 : Real.log (Real.exp X / 3) ≤ Real.log y := Real.log_le_log (by positivity) hy
    rw [Real.log_div (Real.exp_pos X).ne' (by norm_num), Real.log_exp] at h4
    linarith
  have hs : x ^ (ε / 6) / 2 ≤ Real.sqrt (Real.log y) := by
    apply Real.le_sqrt_of_sq_le
    have : (x ^ (ε / 6)) ^ 2 = X := by
      rw [hX, ← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
      congr 1
      push_cast
      ring
    rw [div_pow, this]
    linarith
  have hsplit : x ^ (ε / 6) = x ^ (ε / 8) * x ^ (ε / 24) := by
    rw [← Real.rpow_add hx0]
    congr 1
    ring
  rw [← g_zeta_eq_g_one y]
  calc |Gz y| ≤ K * y * Real.exp (-c * Real.sqrt (Real.log y)) := hK y hy2
    _ ≤ max K 0 * y * Real.exp (-c * Real.sqrt (Real.log y)) := by
        gcongr
        exact le_max_left _ _
    _ ≤ max K 0 * y * Real.exp (-c * (x ^ (ε / 6) / 2)) := by
        have h0 : 0 ≤ max K 0 := le_max_right _ _
        have h5 : Real.exp (-c * Real.sqrt (Real.log y)) ≤ Real.exp (-c * (x ^ (ε / 6) / 2)) :=
          Real.exp_le_exp.2 (by nlinarith)
        exact mul_le_mul_of_nonneg_left h5 (by positivity)
    _ ≤ Real.exp (x ^ (ε / 8) * (c / 2 * x ^ (ε / 24) - c')) * y * Real.exp (-c * (x ^ (ε / 6) / 2)) := by
        gcongr
    _ = y * Real.exp (-c' * x ^ (ε / 8)) := by
        rw [mul_right_comm, ← Real.exp_add, mul_comm]
        congr 2
        rw [hsplit]
        ring
end Formalism.LFunctionChainParameters.LBr2
