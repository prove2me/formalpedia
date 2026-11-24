-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.DividedPowerNorms.bd_pow_incr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:00:02.203869+00:00
-- url     : https://prove2.me/submissions/7f68bfc2-9f22-4c3a-bcf1-7a4cdea26c84

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FirstDeriv
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_LocalComponentGL
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_NormNatCastEqPowPadicValNat
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_IntegralPderivLgF
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DividedPowerNorms_norm_scalar
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
variable {K κ : Type} [NormedField K] [IsUltrametricDist K] [CharZero K] {p : ℕ}
namespace Formalism.InvariantFactorPaths.G7.DividedPowerNorms
theorem _root_.solution (hp : p.Prime) (hnp : ‖(p : K)‖ = (p : ℝ)⁻¹) {A Y : MvPowerSeries κ K}
    (hA : Bd 1 A) (hY : Bd 1 Y) (c : K) (k : ℕ) (hc : ‖(k : K) * c‖ ≤ 1) :
    Bd (p : ℝ)⁻¹ (MvPowerSeries.C c * ((A + MvPowerSeries.C (p : K) * Y) ^ k - A ^ k)) := by
  have hpos : (0 : ℝ) ≤ (p : ℝ)⁻¹ := by positivity
  rcases k with _ | k
  · intro n
    simp
  have e : MvPowerSeries.C c * ((A + MvPowerSeries.C (p : K) * Y) ^ (k + 1) - A ^ (k + 1)) =
      ∑ m ∈ range (k + 1), MvPowerSeries.C (c * ((k + 1).choose (m + 1) : K) * (p : K) ^ (m + 1)) *
        (Y ^ (m + 1) * A ^ (k + 1 - (m + 1))) := by
    rw [add_comm A, add_pow, Finset.sum_range_succ']
    simp only [pow_zero, Nat.choose_zero_right, Nat.cast_one, mul_one, one_mul, Nat.sub_zero]
    rw [add_sub_cancel_right, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    simp only [mul_pow, map_mul, map_pow, map_natCast]
    ring
  rw [e]
  exact bd_sum hpos _ _ fun m _ =>
    sm_mul hpos (bd_C hpos (norm_scalar hp hnp k m hc)) (int_mul (int_pow hY _) (int_pow hA _))
end Formalism.InvariantFactorPaths.G7.DividedPowerNorms
