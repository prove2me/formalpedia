-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.DividedPowerNorms.norm_scalar
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:44:19.489839+00:00
-- url     : https://prove2.me/submissions/fb583cf8-e6a1-4dae-80f0-65246e416545

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FirstDeriv
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_LocalComponentGL
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_NormNatCastEqPowPadicValNat
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_IntegralPderivLgF
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DividedPowerNorms_norm_pow_div
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
theorem _root_.solution [CharZero K] (hp : p.Prime) (hnp : ‖(p : K)‖ = (p : ℝ)⁻¹) {c : K} (k m : ℕ)
    (hc : ‖((k + 1 : ℕ) : K) * c‖ ≤ 1) :
    ‖c * ((k + 1).choose (m + 1) : K) * (p : K) ^ (m + 1)‖ ≤ (p : ℝ)⁻¹ := by
  have hm : ((m + 1 : ℕ) : K) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero m
  have h' : ((k + 1 : ℕ) : K) * (k.choose m : K) =
      ((k + 1).choose (m + 1) : K) * ((m + 1 : ℕ) : K) := by
    exact_mod_cast Nat.add_one_mul_choose_eq k m
  have e : c * ((k + 1).choose (m + 1) : K) * (p : K) ^ (m + 1) =
      (((k + 1 : ℕ) : K) * c) * (k.choose m : K) * ((p : K) ^ (m + 1) / ((m + 1 : ℕ) : K)) := by
    rw [mul_div_assoc', eq_div_iff hm]
    linear_combination (-(c * (p : K) ^ (m + 1))) * h'
  rw [e, norm_mul, norm_mul]
  calc ‖((k + 1 : ℕ) : K) * c‖ * ‖(k.choose m : K)‖ * ‖(p : K) ^ (m + 1) / ((m + 1 : ℕ) : K)‖
      ≤ 1 * 1 * (p : ℝ)⁻¹ :=
        mul_le_mul (mul_le_mul hc (IsUltrametricDist.norm_natCast_le_one K _) (norm_nonneg _)
          zero_le_one) (norm_pow_div hp hnp m) (norm_nonneg _) (by norm_num)
    _ = (p : ℝ)⁻¹ := by ring
end Formalism.InvariantFactorPaths.G7.DividedPowerNorms
