-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.DworkIntegrality.small_of_exp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T09:45:15.139786+00:00
-- url     : https://prove2.me/submissions/d3c29317-7897-4d23-b960-e9eb04bfdc13

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_CyclicPowerClassOfExpEquiv
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartB
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_LocalComponentGL
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_bd_sub
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_low_sub_truncD
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_coeff_truncD_self
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_constantCoeff_truncD
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_coeff_eq_of_low
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_bd_induct
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_constantCoeff_mvExp
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_low_exp_sub
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_exp_small
import Theorems.Thm_Formalism_FG_SolveVAux_low_add
import Theorems.Thm_Formalism_FG_SolveVAux_low_mono
import Theorems.Thm_Formalism_FG_SolveVAux_low_mul
import Theorems.Thm_Formalism_FG_SolveVAux_low_neg
import Theorems.Thm_Formalism_FG_SolveVAux_low_one_iff
import Theorems.Thm_Formalism_FG_SolveVAux_low_pow
import Theorems.Thm_Formalism_FG_SolveVAux_low_sub
import Theorems.Thm_Formalism_FG_SolveVAux_low_zero
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_mvExp_add


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
theorem _root_.solution [Finite ι] (hp : p.Prime) (hnp : ‖(p : K)‖ = (p : ℝ)⁻¹)
    {D : MvPowerSeries ι K} (hD0 : MvPowerSeries.constantCoeff D = 0)
    (hD : Bd (p : ℝ)⁻¹ (mvExp D - 1)) : Bd (p : ℝ)⁻¹ D := by
  have hpos : (0 : ℝ) ≤ (p : ℝ)⁻¹ := by positivity
  refine bd_induct hpos D fun d hl m hm => ?_
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · have hm0 : m = 0 := (Finsupp.degree_eq_zero_iff m).1 hm
    rw [hm0, MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hD0]
    simp
  have hDh : Low d (D - truncD d D) := low_sub_truncD d D
  have hDl0 : MvPowerSeries.constantCoeff (truncD d D) = 0 := by
    rw [constantCoeff_truncD hd, hD0]
  have hDh0 : MvPowerSeries.constantCoeff (D - truncD d D) = 0 := by
    rw [map_sub, hD0, hDl0, sub_zero]
  have hEl := exp_small hp hnp hDl0 hl
  have hEl1 : Low 1 (mvExp (truncD d D) - 1) :=
    (low_one_iff _).2 (by rw [map_sub, constantCoeff_mvExp hDl0]; simp)
  have hEh := low_exp_sub hd hDh
  have hadd : mvExp D = mvExp (truncD d D) * mvExp (D - truncD d D) := by
    rw [← mvExp_add hDl0 hDh0]; congr 1; ring
  have hlow : Low (d + 1) (D - ((mvExp D - 1) - (mvExp (truncD d D) - 1) + truncD d D)) := by
    have e : D - ((mvExp D - 1) - (mvExp (truncD d D) - 1) + truncD d D) =
        -((mvExp (D - truncD d D) - 1 - (D - truncD d D)) * mvExp (truncD d D) +
          (mvExp (truncD d D) - 1) * (D - truncD d D)) := by
      rw [hadd]; ring
    rw [e]
    refine low_neg (low_add ?_ ?_)
    · simpa using low_mul hEh (low_zero (mvExp (truncD d D)))
    · have := low_mul hEl1 hDh
      rwa [add_comm] at this
  rw [coeff_eq_of_low hlow hm, map_add, coeff_truncD_self D hm, add_zero]
  exact bd_sub hD hEl m
end Formalism.InvariantFactorPaths.G7.DworkIntegrality
