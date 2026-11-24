-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.CoefficientSupportCongruences.partial_coboundary_de_s_g_series
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:42:49.05699+00:00
-- url     : https://prove2.me/submissions/3b2e57ca-fd53-4449-bf81-09755af18e69

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_ThmSUniform
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FinalS
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_FrobeniusPartialCoboundaryBound
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_CoefficientSupportCongruences_DeS_Gser
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_CoboundarySeries_partial_coboundary_C_mul
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_CoboundarySeries_partial_coboundary_h_series
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_PhiH_apply
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_bd_C
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_bd_add
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_bd_mul
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_bd_neg
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_bd_sub
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_frob_congr
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_int_mul
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_int_pow
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoVariableSwapLemmas_partial_coboundary_C_mul


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
open DworkIntegrality (Bd bd_add bd_sub bd_neg bd_mul bd_C int_mul int_pow frob_congr PhiH PhiH_apply)
open Formalism.InvariantFactorPaths.G7.CoefficientSupportCongruences
open FrobeniusSubstitution
variable {K : Type} [Field K]
namespace Formalism.InvariantFactorPaths.G7.CoefficientSupportCongruences
theorem _root_.solution {p : ℕ} (hp : 2 ≤ p) (hpK : (p : K) ≠ 0) (σ : K →+* K) {c : K}
    (hσσ : σ (σ c) = c) {F : MvPowerSeries (Fin 2) K}
    (hF0 : MvPowerSeries.constantCoeff F = 0) (hl : cob F (lgF K p) = 0) :
    d1 F (DeS p σ (Gser p c (σ c))) =
      MvPowerSeries.C (σ c) * (in3 (cob F (g0F K p)) * at1 2 (lgF K p)) := by
  have hH : Hser p σ (Gser p c (σ c)) (σ c) (-c) = 0 := by
    unfold Hser
    rw [DeS_Gser hp hpK σ hσσ, map_neg]
    ring
  have h0 : d1 F (0 : MvPowerSeries (Fin 2) K) = 0 := by
    have h := Formalism.InvariantFactorPaths.G7.TwoVariableSwapLemmas.partial_coboundary_C_mul hF0 (0 : K) 0
    simpa using h
  have h := Formalism.InvariantFactorPaths.G7.CoboundarySeries.partial_coboundary_h_series (p := p) σ hF0 hl (Gser p c (σ c)) (σ c) (-c)
  rw [hH, h0] at h
  exact sub_eq_zero.mp h.symm
end Formalism.InvariantFactorPaths.G7.CoefficientSupportCongruences
