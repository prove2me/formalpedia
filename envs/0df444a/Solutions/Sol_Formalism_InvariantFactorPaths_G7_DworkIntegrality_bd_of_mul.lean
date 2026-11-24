-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.DworkIntegrality.bd_of_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:06:47.334697+00:00
-- url     : https://prove2.me/submissions/f123e0c6-1ee7-4952-bab8-56612ca63028

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_CyclicPowerClassOfExpEquiv
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartB
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_LocalComponentGL
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_bd_sub
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_sm_mul
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_low_sub_truncD
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_coeff_truncD_self
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_coeff_eq_of_low
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_bd_induct
import Theorems.Thm_Formalism_FG_SolveVAux_low_add
import Theorems.Thm_Formalism_FG_SolveVAux_low_mono
import Theorems.Thm_Formalism_FG_SolveVAux_low_mul
import Theorems.Thm_Formalism_FG_SolveVAux_low_neg
import Theorems.Thm_Formalism_FG_SolveVAux_low_one_iff
import Theorems.Thm_Formalism_FG_SolveVAux_low_pow
import Theorems.Thm_Formalism_FG_SolveVAux_low_sub
import Theorems.Thm_Formalism_FG_SolveVAux_low_zero


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
variable {K ι : Type} [NormedField K] [Finite ι]
variable [IsUltrametricDist K]
namespace Formalism.InvariantFactorPaths.G7.DworkIntegrality
theorem _root_.solution {c : ℝ} (hc : 0 ≤ c) {X U : MvPowerSeries ι K} (hU : Bd 1 U)
    (hU1 : MvPowerSeries.constantCoeff U = 1) (h : Bd c (X * U)) : Bd c X := by
  refine bd_induct hc X fun d hl m hm => ?_
  have hXh := low_sub_truncD d X
  have hU' : Low 1 (U - 1) := (low_one_iff _).2 (by simp [hU1])
  have hlow : Low (d + 1) (X - (X * U - truncD d X * U + truncD d X)) := by
    have e : X - (X * U - truncD d X * U + truncD d X) = -((X - truncD d X) * (U - 1)) := by ring
    rw [e]
    exact low_neg (low_mul hXh hU')
  rw [coeff_eq_of_low hlow hm, map_add, coeff_truncD_self X hm, add_zero]
  exact bd_sub h (sm_mul hc hl hU) m
end Formalism.InvariantFactorPaths.G7.DworkIntegrality
