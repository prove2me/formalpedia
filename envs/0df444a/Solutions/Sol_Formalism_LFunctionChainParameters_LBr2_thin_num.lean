-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LBr2.thin_num
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T02:36:25.025297+00:00
-- url     : https://prove2.me/submissions/b6dd869b-73cb-46a6-860c-ae4719f28eab

import Definitions.Def_Formalism_SizeWindowBrackets_SmoothedRemainderRealIntegralFormula
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_GaloisMapComplexConjugation
import Definitions.Def_Formalism_LandauZeroFreeBounds_SiegelWalfiszAPOfSiegelLower
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_PrimeCongruenceConditions
import Theorems.Thm_Formalism_LFunctionChainParameters_LBr2_thin_caseA
import Theorems.Thm_Formalism_LFunctionChainParameters_LBr2_thin_caseB

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
theorem _root_.solution (ε a A : ℝ) (hε : 0 < ε) (ha : 0 < a) (hA : 0 ≤ A) :
    ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → ∀ μ v : ℝ, 2 ≤ μ → μ ≤ 2 * x ^ (ε / 5) * Real.log x ^ 2 + 2 → x ^ (ε / 3) / 2 ≤ v →
      A * (μ + Real.sqrt v + v) ^ 3 * Real.exp (-a * v / (μ + Real.sqrt v)) ≤ Real.exp (-(a / 16) * x ^ (ε / 8)) := by
  set K6 : ℝ := ((6 : ℕ).factorial : ℝ) / (a / 4) ^ 6 with hK6
  set K10 : ℝ := ((10 : ℕ).factorial : ℝ) / (a / 8) ^ 10 with hK10
  have TR : Tendsto (fun x : ℝ => x ^ (ε / 8)) atTop atTop := tendsto_rpow_atTop (by positivity)
  have E1 : ∀ᶠ x : ℝ in atTop, 1 ≤ x := eventually_ge_atTop 1
  have E2 : ∀ᶠ x : ℝ in atTop, 8 ≤ x ^ (ε / 3) := (tendsto_rpow_atTop (by positivity : 0 < ε / 3)).eventually_ge_atTop 8
  have E3 : ∀ᶠ x : ℝ in atTop, ‖Real.log x‖ ≤ 1 / 2 * ‖x ^ (ε / 480)‖ :=
    (isLittleO_log_rpow_atTop (by positivity : 0 < ε / 480)).bound (by norm_num)
  have E4 : ∀ᶠ x : ℝ in atTop, 4 ≤ x ^ (5 * ε / 24) :=
    (tendsto_rpow_atTop (by positivity : 0 < 5 * ε / 24)).eventually_ge_atTop 4
  have E5 : ∀ᶠ x : ℝ in atTop, max (8 * A * K6) (8 * A * K10) ≤ Real.exp (a / 16 * x ^ (ε / 8)) :=
    (Real.tendsto_exp_atTop.comp (TR.const_mul_atTop (by positivity : 0 < a / 16))).eventually_ge_atTop _
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.1 (E1.and (E2.and (E3.and (E4.and E5))))
  refine ⟨x₀, fun x hx μ v hμ2 hμ hv => ?_⟩
  obtain ⟨h1, h2, h3, h4, h5⟩ := hx₀ x hx
  have hx0 : 0 < x := by linarith
  obtain ⟨R, hR⟩ : ∃ R : ℝ, R = x ^ (ε / 8) := ⟨_, rfl⟩
  obtain ⟨Lb, hLb⟩ : ∃ Lb : ℝ, Lb = x ^ (5 * ε / 24) := ⟨_, rfl⟩
  rw [← hR] at h5 ⊢
  rw [← hLb] at h4
  have hR1 : 1 ≤ R := hR ▸ Real.one_le_rpow h1 (by positivity)
  have hRL : R ≤ Lb := by
    rw [hR, hLb]
    exact Real.rpow_le_rpow_of_exponent_le h1 (by linarith)
  have hP3 : x ^ (ε / 3) = Lb * R := by
    rw [hLb, hR, ← Real.rpow_add hx0]
    congr 1
    ring
  have hL6 : Lb ^ 6 = R ^ 10 := by
    rw [hLb, hR, ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul hx0.le, ← Real.rpow_mul hx0.le]
    congr 1
    push_cast
    ring
  have hμL : μ ≤ Lb := by
    have hp : 0 ≤ x ^ (ε / 480) := by positivity
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hp] at h3
    have hlog2 : Real.log x ^ 2 ≤ 1 / 4 * x ^ (ε / 240) := by
      have e : x ^ (ε / 240) = x ^ (ε / 480) * x ^ (ε / 480) := by
        rw [← Real.rpow_add hx0]; congr 1; ring
      rw [e, ← sq_abs]
      nlinarith [abs_nonneg (Real.log x)]
    have h6 : x ^ (ε / 5) * x ^ (ε / 240) ≤ Lb := by
      rw [← Real.rpow_add hx0, hLb]
      apply Real.rpow_le_rpow_of_exponent_le h1
      linarith
    have hp5 : 0 ≤ x ^ (ε / 5) := by positivity
    have h7 : 2 * x ^ (ε / 5) * Real.log x ^ 2 ≤ 1 / 2 * Lb := by
      calc 2 * x ^ (ε / 5) * Real.log x ^ 2 ≤ 2 * x ^ (ε / 5) * (1 / 4 * x ^ (ε / 240)) := by gcongr
        _ = 1 / 2 * (x ^ (ε / 5) * x ^ (ε / 240)) := by ring
        _ ≤ 1 / 2 * Lb := by gcongr
    linarith
  have hv4 : 4 ≤ v := by linarith
  have hv0 : 0 ≤ v := by linarith
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s = Real.sqrt v := ⟨_, rfl⟩
  have hsv : v = s ^ 2 := by rw [hs]; exact (Real.sq_sqrt hv0).symm
  have hs2 : 2 ≤ s := by
    rw [hs]
    apply Real.le_sqrt_of_sq_le
    linarith
  rw [← hs, hsv]
  have hvL : Lb * R / 2 ≤ s ^ 2 := by rw [← hsv, ← hP3]; exact hv
  have hfin : ∀ Kc : ℝ, 8 * A * Kc ≤ Real.exp (a / 16 * R) →
      8 * A * Kc * Real.exp (-(a / 8 * R)) ≤ Real.exp (-(a / 16) * R) := by
    intro Kc hKc
    calc 8 * A * Kc * Real.exp (-(a / 8 * R)) ≤ Real.exp (a / 16 * R) * Real.exp (-(a / 8 * R)) :=
          mul_le_mul_of_nonneg_right hKc (Real.exp_pos _).le
      _ = Real.exp (-(a / 16) * R) := by rw [← Real.exp_add]; congr 1; ring
  by_cases hcase : μ ≤ s
  · have hsR : R / 2 ≤ s := by
      have h13 : (R / 2) ^ 2 ≤ s ^ 2 := by
        have h14 : R * R ≤ Lb * R := mul_le_mul_of_nonneg_right hRL (by linarith)
        nlinarith
      exact (abs_le_of_sq_le_sq' h13 (by linarith)).2
    exact (thin_caseA a A μ s R ha hA hμ2 hcase hsR).trans (hfin K6 (le_trans (le_max_left _ _) h5))
  · rw [not_le] at hcase
    exact (thin_caseB a A μ s R Lb ha hA hμ2 (by linarith) hcase hμL hvL hL6 (by linarith)).trans
      (hfin K10 (le_trans (le_max_right _ _) h5))
end Formalism.LFunctionChainParameters.LBr2
