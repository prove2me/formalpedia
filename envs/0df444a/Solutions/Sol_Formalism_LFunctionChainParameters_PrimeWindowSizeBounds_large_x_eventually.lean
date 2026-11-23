-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.PrimeWindowSizeBounds.large_x_eventually
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:37:06.673803+00:00
-- url     : https://prove2.me/submissions/997fcefc-c010-4b02-ac86-ac62f63eedf3

import Definitions.Def_Formalism_SizeWindowBrackets_WindowSettingSatisfiable
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_AdmissibleSchurLemma
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_OneLeThresholdMulPowers
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_Facts_xpos

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.PrimeWindowSizeBounds
open Finset Classical
open Formalism.LFunctionChainParameters.DeficitSplitLemmas Formalism.LFunctionChainParameters.LErr
namespace Formalism.LFunctionChainParameters.PrimeWindowSizeBounds
theorem _root_.solution : LargeXEv := by
  intro ε e K hε hε4
  have hε3 : 0 < ε / 3 := by positivity
  have hC : ∀ᶠ x : ℝ in Filter.atTop, 100 * K * x ^ (4 * ε) ≤ x := by
    have h := (tendsto_rpow_atTop (show 0 < 1 - 4 * ε by linarith)).eventually_ge_atTop (100 * K)
    filter_upwards [h, Filter.eventually_ge_atTop (1 : ℝ)] with x hx hx1
    have xpos : 0 < x := by linarith
    calc 100 * K * x ^ (4 * ε) ≤ x ^ (1 - 4 * ε) * x ^ (4 * ε) :=
          mul_le_mul_of_nonneg_right hx (Real.rpow_nonneg xpos.le _)
      _ = x := by
          rw [← Real.rpow_add xpos]
          have : 1 - 4 * ε + 4 * ε = 1 := by ring
          rw [this, Real.rpow_one]
  have hB : ∀ᶠ x : ℝ in Filter.atTop, 100 * K * x ^ (4 * e + 4) ≤ Real.exp (x ^ (ε / 3)) := by
    have hc : 0 < (2 * (|4 * e + 4| + 1))⁻¹ := by positivity
    have hb := (isLittleO_log_rpow_atTop hε3).bound hc
    have hA := (tendsto_rpow_atTop hε3).eventually_ge_atTop (2 * Real.log (100 * (|K| + 1)))
    filter_upwards [hb, hA, Filter.eventually_ge_atTop (1 : ℝ)] with x hx hxA hx1
    have xpos : 0 < x := by linarith
    rw [Real.norm_of_nonneg (Real.rpow_nonneg xpos.le _),
      Real.norm_of_nonneg (Real.log_nonneg hx1)] at hx
    have hlog0 := Real.log_nonneg hx1
    have h1 : (|4 * e + 4| + 1) * Real.log x ≤ x ^ (ε / 3) / 2 := by
      have h2 : (|4 * e + 4| + 1) * Real.log x
          ≤ (|4 * e + 4| + 1) * ((2 * (|4 * e + 4| + 1))⁻¹ * x ^ (ε / 3)) := by gcongr
      have h3 : (|4 * e + 4| + 1) * ((2 * (|4 * e + 4| + 1))⁻¹ * x ^ (ε / 3)) = x ^ (ε / 3) / 2 := by
        have : |4 * e + 4| + 1 ≠ 0 := by positivity
        field_simp
      linarith
    have h4 : Real.log x * (4 * e + 4) ≤ x ^ (ε / 3) / 2 := by
      have h5 : Real.log x * (4 * e + 4) ≤ Real.log x * (|4 * e + 4| + 1) := by
        have := le_abs_self (4 * e + 4)
        exact mul_le_mul_of_nonneg_left (by linarith) hlog0
      linarith
    have hKpos : 0 < 100 * (|K| + 1) := by positivity
    calc 100 * K * x ^ (4 * e + 4) ≤ 100 * (|K| + 1) * x ^ (4 * e + 4) := by
          have := le_abs_self K
          have := Real.rpow_nonneg xpos.le (4 * e + 4)
          gcongr
          linarith
      _ = Real.exp (Real.log (100 * (|K| + 1)) + Real.log x * (4 * e + 4)) := by
          rw [Real.exp_add, Real.exp_log hKpos, Real.rpow_def_of_pos xpos]
      _ ≤ Real.exp (x ^ (ε / 3)) := Real.exp_le_exp.2 (by linarith)
  have h6 : ∀ᶠ x : ℝ in Filter.atTop, (6 : ℝ) ≤ x ^ (2 * ε / 3) :=
    (tendsto_rpow_atTop (by positivity)).eventually_ge_atTop _
  obtain ⟨x0, hx0⟩ :=
    Filter.eventually_atTop.1 (((hC.and hB).and h6).and (Filter.eventually_ge_atTop (1 : ℝ)))
  refine ⟨x0, fun x hx => ?_⟩
  obtain ⟨⟨⟨c1, c2⟩, c3⟩, c4⟩ := hx0 x hx
  have xpos : 0 < x := by linarith
  refine ⟨c4, c1, c2, ?_⟩
  have hw0 : 0 ≤ x ^ (ε / 3) := Real.rpow_nonneg xpos.le _
  have h43 : x ^ (ε / 4) ≤ x ^ (ε / 3) := Real.rpow_le_rpow_of_exponent_le c4 (by linarith)
  have hz : x ^ ε = x ^ (2 * ε / 3) * x ^ (ε / 3) := by
    rw [← Real.rpow_add xpos]; congr 1; ring
  have hz6 : 6 * x ^ (ε / 3) ≤ x ^ ε := by rw [hz]; gcongr
  calc 100 * K * x ^ (4 * e + 4) * Real.exp (x ^ (ε / 3) + x ^ (ε / 4))
      ≤ Real.exp (x ^ (ε / 3)) * Real.exp (x ^ (ε / 3) + x ^ (ε / 4)) :=
        mul_le_mul_of_nonneg_right c2 (Real.exp_pos _).le
    _ = Real.exp (x ^ (ε / 3) + (x ^ (ε / 3) + x ^ (ε / 4))) := (Real.exp_add _ _).symm
    _ ≤ Real.exp (x ^ ε / 2) := Real.exp_le_exp.2 (by linarith)
end Formalism.LFunctionChainParameters.PrimeWindowSizeBounds
