-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.DividedPowerNorms.norm_coeff_lgF_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:44:18.53031+00:00
-- url     : https://prove2.me/submissions/3d2fef7c-4e2b-4912-bc95-4e07620164b3

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FirstDeriv
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_LocalComponentGL
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_NormNatCastEqPowPadicValNat
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_IntegralPderivLgF
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DividedPowerNorms_norm_p_pos
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DividedPowerNorms_norm_p_pow_le_one
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_PhiH_apply
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_bd_C
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_bd_add
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_bd_mul
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_bd_natCast
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_bd_sub
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_bd_sum
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_frob_congr
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_int_mul
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_int_pow
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_sm_mul
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_coeff_lgF_ne_zero
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_coeff_lgF_pow


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
open DworkIntegrality (Bd bd_add bd_sub bd_mul bd_C bd_sum int_mul int_pow sm_mul bd_natCast frob_congr
  PhiH PhiH_apply)
open DividedPowerNorms
open Formalism.InvariantFactorPaths.G7.DividedPowerNorms
namespace Formalism.InvariantFactorPaths.G7.DividedPowerNorms
theorem _root_.solution {K : Type} [NormedField K] [IsUltrametricDist K] {p : ℕ} (hp : p.Prime)
    (hnp : ‖(p : K)‖ = (p : ℝ)⁻¹) (N : ℕ) : ‖PowerSeries.coeff N (lgF K p) * (N : K)‖ ≤ 1 := by
  have hpK : (p : K) ≠ 0 := norm_pos_iff.mp (norm_p_pos hp hnp)
  by_cases h : PowerSeries.coeff N (lgF K p) = 0
  · simp [h]
  obtain ⟨j, rfl⟩ := coeff_lgF_ne_zero h
  rw [coeff_lgF_pow K hp.two_le]
  have e : ((p : K) ^ j)⁻¹ * (((p ^ 2) ^ j : ℕ) : K) = (p : K) ^ j := by
    push_cast
    field_simp
    ring
  rw [e]
  exact norm_p_pow_le_one hp hnp j
end Formalism.InvariantFactorPaths.G7.DividedPowerNorms
