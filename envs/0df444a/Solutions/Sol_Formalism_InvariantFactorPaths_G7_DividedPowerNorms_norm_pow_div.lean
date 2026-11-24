-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.DividedPowerNorms.norm_pow_div
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:28:36.47954+00:00
-- url     : https://prove2.me/submissions/1ea07c06-7f83-4b02-882f-5413e1c7eb0e

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FirstDeriv
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_LocalComponentGL
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_NormNatCastEqPowPadicValNat
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_IntegralPderivLgF
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DividedPowerNorms_norm_p_lt_one
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DividedPowerNorms_norm_p_pos
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_norm_natCast_eq_pow_padicValNat
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
open Formalism.InvariantFactorPaths.G7.DividedPowerNorms
variable {K : Type} [NormedField K] [IsUltrametricDist K] {p : ℕ}
namespace Formalism.InvariantFactorPaths.G7.DividedPowerNorms
theorem _root_.solution (hp : p.Prime) (hnp : ‖(p : K)‖ = (p : ℝ)⁻¹) (m : ℕ) :
    ‖(p : K) ^ (m + 1) / ((m + 1 : ℕ) : K)‖ ≤ (p : ℝ)⁻¹ := by
  have hlt := norm_p_lt_one (K := K) hp hnp
  have hpos := norm_p_pos (K := K) hp hnp
  rw [norm_div, norm_pow,
    Formalism.DworkPowerSeriesWeights.norm_natCast_eq_pow_padicValNat hp hlt (show m + 1 ≠ 0 by omega)]
  have hv : padicValNat p (m + 1) ≤ m := by
    have h1 : p ^ padicValNat p (m + 1) ∣ m + 1 := pow_padicValNat_dvd
    have h2 := Nat.le_of_dvd (Nat.succ_pos m) h1
    have h3 : padicValNat p (m + 1) < p ^ padicValNat p (m + 1) := Nat.lt_pow_self hp.one_lt
    omega
  rw [div_le_iff₀ (pow_pos hpos _), ← hnp, ← pow_succ']
  exact pow_le_pow_of_le_one hpos.le hlt.le (by omega)
end Formalism.InvariantFactorPaths.G7.DividedPowerNorms
