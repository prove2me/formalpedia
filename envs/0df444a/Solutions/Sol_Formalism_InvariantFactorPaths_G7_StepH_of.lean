-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.StepH_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:00:48.727858+00:00
-- url     : https://prove2.me/submissions/e952c17c-2c76-48fc-870c-9446d94d7cd4

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FirstDeriv
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_ConstantCoeffFirstTwoOfThree
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_CoboundarySeries_partial_coboundary_h_series
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_CoboundarySeries_suppOK_Hser
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_CoboundarySeries_coeff_lg_lg_eq_zero

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
open CoboundarySeries
namespace Formalism.InvariantFactorPaths.G7
theorem _root_.solution (h2 : LemmaTwo) (hSw : SwapRules) (_hL : LawSymm) : StepH := by
  intro K _ _ _ _ p σ hU F hF G γ γ' hG hI1 hI2
  have hp : 2 ≤ p := hU.2.1.le
  obtain ⟨-, -, -, -, -, hHsw⟩ := hSw K p σ G γ γ' hp
  have hsupp : SuppOK p (Hser p σ G γ γ') := suppOK_Hser hp σ hG γ γ'
  have hdiv : DivAB (Hser p σ G γ γ') := by
    intro n hn
    by_contra hc
    obtain ⟨h0, h1, -⟩ := hsupp n hc
    omega
  have hd1 : Integral (d1 F (Hser p σ G γ γ')) := by
    rw [partial_coboundary_h_series σ hF.1 hF.2.2 G γ γ']
    exact hI1
  have hd2 : Integral (d1 F (swap2 (Hser p σ G γ γ'))) := by
    rw [← hHsw, partial_coboundary_h_series σ hF.1 hF.2.2 (swap2 G) γ' γ]
    exact hI2
  obtain ⟨β, R, hR, hHR⟩ := h2 K p σ hU F hF _ hdiv hd1 hd2
  intro n
  by_cases hc : MvPowerSeries.coeff n (Hser p σ G γ γ') = 0
  · rw [hc, norm_zero]
    exact zero_le_one
  · have hll := coeff_lg_lg_eq_zero (K := K) hp (hsupp n hc).2.2
    rw [hHR, map_add, MvPowerSeries.coeff_C_mul, hll, mul_zero, zero_add]
    exact hR n
end Formalism.InvariantFactorPaths.G7
