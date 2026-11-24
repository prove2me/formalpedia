-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.FrobeniusSubstitution.subst_g_zero_eq_log
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:12:38.717009+00:00
-- url     : https://prove2.me/submissions/f67e5aa7-cf7e-4565-9e1b-8b1b2cea9e53

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FirstDeriv
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_LocalComponentGL
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_LogarithmEquivalence
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ChainRule
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_PartialCoboundaryLinear
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_PhiH_apply
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_bd_C
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_bd_add
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_bd_mul
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_bd_neg
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_bd_sub
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_frob_congr
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_int_mul
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_int_pow
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_g_zero_relation_holds


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
theorem _root_.solution {ι : Type} {p : ℕ} (hp : 2 ≤ p) (hpK : (p : K) ≠ 0) {a : MvPowerSeries ι K}
    (ha : PowerSeries.HasSubst a) :
    PowerSeries.subst a (g0F K p) =
      MvPowerSeries.C ((p : K)⁻¹) * PowerSeries.subst (a ^ p) (lgF K p) := by
  have hsXp : PowerSeries.HasSubst (PowerSeries.X ^ p : PowerSeries K) :=
    PowerSeries.HasSubst.X_pow (by omega)
  rw [(g_zero_relation_holds K p hp hpK).1, PowerSeries.subst_mul ha, PowerSeries.subst_C,
    PowerSeries.subst_comp_subst_apply hsXp ha, PowerSeries.subst_pow ha, PowerSeries.subst_X ha]
end Formalism.InvariantFactorPaths.G7.FrobeniusSubstitution
