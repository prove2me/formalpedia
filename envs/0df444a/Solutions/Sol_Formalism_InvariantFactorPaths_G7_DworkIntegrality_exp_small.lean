-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.DworkIntegrality.exp_small
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T09:41:23.752427+00:00
-- url     : https://prove2.me/submissions/90240929-f631-4fbe-8633-2710e80229d5

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_CyclicPowerClassOfExpEquiv
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartB
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_LocalComponentGL
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_bd_pow
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_norm_fact_bound
import Theorems.Thm_Formalism_FG_SolveVAux_low_add
import Theorems.Thm_Formalism_FG_SolveVAux_low_mono
import Theorems.Thm_Formalism_FG_SolveVAux_low_mul
import Theorems.Thm_Formalism_FG_SolveVAux_low_neg
import Theorems.Thm_Formalism_FG_SolveVAux_low_one_iff
import Theorems.Thm_Formalism_FG_SolveVAux_low_pow
import Theorems.Thm_Formalism_FG_SolveVAux_low_sub
import Theorems.Thm_Formalism_FG_SolveVAux_low_zero
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_coeff_mvExp


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
open Formalism.FG.SolveVAux (Low low_zero low_mono low_add low_sub low_neg low_mul low_pow low_one_iff)
open Formalism.InvariantFactorPaths.G7.DworkIntegrality
variable {K ι : Type} [NormedField K] [CharZero K]
variable [IsUltrametricDist K] {p : ℕ}
namespace Formalism.InvariantFactorPaths.G7.DworkIntegrality
theorem _root_.solution (hp : p.Prime) (hnp : ‖(p : K)‖ = (p : ℝ)⁻¹) {u : MvPowerSeries ι K}
    (hu0 : MvPowerSeries.constantCoeff u = 0) (hu : Bd (p : ℝ)⁻¹ u) :
    Bd (p : ℝ)⁻¹ (mvExp u - 1) := by
  have hpos : (0 : ℝ) ≤ (p : ℝ)⁻¹ := by positivity
  intro n
  rw [map_sub, coeff_mvExp hu0, Finset.sum_range_succ']
  have e0 : ((Nat.factorial 0 : ℕ) : K)⁻¹ * MvPowerSeries.coeff n (u ^ 0) =
      MvPowerSeries.coeff n (1 : MvPowerSeries ι K) := by simp
  rw [e0, add_sub_cancel_right]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hpos fun k _ => ?_
  rw [norm_mul]
  exact (mul_le_mul_of_nonneg_left (bd_pow hpos hu (k + 1) n) (norm_nonneg _)).trans
    (norm_fact_bound hp hnp k)
end Formalism.InvariantFactorPaths.G7.DworkIntegrality
