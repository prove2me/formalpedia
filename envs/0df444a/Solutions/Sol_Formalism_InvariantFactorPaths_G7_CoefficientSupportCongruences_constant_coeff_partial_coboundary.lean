-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.CoefficientSupportCongruences.constant_coeff_partial_coboundary
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:25:04.866814+00:00
-- url     : https://prove2.me/submissions/e74234c5-e2f0-464e-a3e8-db5f97864d10

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_ThmSUniform
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FinalS
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_FrobeniusPartialCoboundaryBound
import Theorems.Thm_Formalism_G_LogP_constantCoeff_subst_of_zero
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_PhiH_apply
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_bd_C
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_bd_add
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_bd_mul
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_bd_neg
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_bd_sub
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_frob_congr
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_int_mul
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_int_pow


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
theorem _root_.solution {F G : MvPowerSeries (Fin 2) K}
    (hF0 : MvPowerSeries.constantCoeff F = 0) (hG0 : MvPowerSeries.constantCoeff G = 0) :
    MvPowerSeries.constantCoeff (d1 F G) = 0 := by
  have hin : MvPowerSeries.constantCoeff (in3 F) = 0 := by
    show MvPowerSeries.constantCoeff (MvPowerSeries.subst
      ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 3) K), MvPowerSeries.X 1] F) = 0
    rw [Formalism.G.LogP.constantCoeff_subst_of_zero F, hF0]
    intro i; fin_cases i <;> simp
  have e1 : MvPowerSeries.constantCoeff (MvPowerSeries.subst
      ![in3 F, (MvPowerSeries.X 2 : MvPowerSeries (Fin 3) K)] G) = 0 := by
    rw [Formalism.G.LogP.constantCoeff_subst_of_zero G, hG0]
    intro i; fin_cases i <;> simp [hin]
  have e2 : MvPowerSeries.constantCoeff (MvPowerSeries.subst
      ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 3) K), MvPowerSeries.X 2] G) = 0 := by
    rw [Formalism.G.LogP.constantCoeff_subst_of_zero G, hG0]
    intro i; fin_cases i <;> simp
  have e3 : MvPowerSeries.constantCoeff (MvPowerSeries.subst
      ![(MvPowerSeries.X 1 : MvPowerSeries (Fin 3) K), MvPowerSeries.X 2] G) = 0 := by
    rw [Formalism.G.LogP.constantCoeff_subst_of_zero G, hG0]
    intro i; fin_cases i <;> simp
  show MvPowerSeries.constantCoeff (MvPowerSeries.subst
      ![in3 F, (MvPowerSeries.X 2 : MvPowerSeries (Fin 3) K)] G -
    MvPowerSeries.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 3) K), MvPowerSeries.X 2] G -
    MvPowerSeries.subst ![(MvPowerSeries.X 1 : MvPowerSeries (Fin 3) K), MvPowerSeries.X 2] G) = 0
  rw [map_sub, map_sub, e1, e2, e3]
  simp
end Formalism.InvariantFactorPaths.G7.CoefficientSupportCongruences
