-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.FrobeniusSubstitution.pderiv_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:29:35.374797+00:00
-- url     : https://prove2.me/submissions/5f74d18e-d100-4105-a383-8c0f7a8a1e72

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FirstDeriv
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_LocalComponentGL
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_LogarithmEquivalence
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ChainRule
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_PartialCoboundaryLinear
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_FrobeniusSubstitution_pderiv_single_self
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_FrobeniusSubstitution_pderiv_single_ne
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
open Formalism.InvariantFactorPaths.G7.FrobeniusSubstitution
variable {K : Type} [Field K]
namespace Formalism.InvariantFactorPaths.G7.FrobeniusSubstitution
theorem _root_.solution (k : K) (f g : PowerSeries K) :
    MvPowerSeries.pderiv K (0 : Fin 2) (MvPowerSeries.C k * (at1 0 f * at1 1 g)) =
      MvPowerSeries.C k * (at1 0 (PowerSeries.derivative K f) * at1 1 g) := by
  have hC : MvPowerSeries.pderiv K (0 : Fin 2) (MvPowerSeries.C k) = 0 := by
    ext n
    simp [MvPowerSeries.coeff_pderiv, MvPowerSeries.coeff_C]
  have h10 : (1 : Fin 2) ≠ 0 := by decide
  simp only [Derivation.leibniz, hC, pderiv_single_self, pderiv_single_ne h10, smul_zero, add_zero, zero_add,
    smul_eq_mul]
  ring
end Formalism.InvariantFactorPaths.G7.FrobeniusSubstitution
