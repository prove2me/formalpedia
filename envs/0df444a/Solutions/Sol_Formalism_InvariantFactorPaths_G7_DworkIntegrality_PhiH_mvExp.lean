-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.DworkIntegrality.PhiH_mvExp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:06:47.500814+00:00
-- url     : https://prove2.me/submissions/882c3079-be67-4c8f-be0f-5229db01aae7

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_CyclicPowerClassOfExpEquiv
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartB
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_LocalComponentGL
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_PhiH_apply
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
variable {K ι : Type} [NormedField K] [CharZero K]
namespace Formalism.InvariantFactorPaths.G7.DworkIntegrality
theorem _root_.solution {p : ℕ} (hp : p ≠ 0) (σ : K →+* K) {Ψ : MvPowerSeries ι K}
    (h0 : MvPowerSeries.constantCoeff Ψ = 0) :
    PhiH hp σ (mvExp Ψ) = mvExp (PhiH hp σ Ψ) := by
  have h1 : MvPowerSeries.map σ (mvExp Ψ) = mvExp (MvPowerSeries.map σ Ψ) := by
    unfold mvExp
    rw [PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero h0), PowerSeries.map_exp]
  have h0' : MvPowerSeries.constantCoeff (MvPowerSeries.map σ Ψ) = 0 := by
    rw [MvPowerSeries.constantCoeff_map, h0, map_zero]
  rw [PhiH_apply, PhiH_apply, h1]
  unfold frobVar mvExp
  rw [PowerSeries.subst_def, PowerSeries.subst_def,
    MvPowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero h0').const
      (MvPowerSeries.HasSubst.X_pow hp)]
end Formalism.InvariantFactorPaths.G7.DworkIntegrality
