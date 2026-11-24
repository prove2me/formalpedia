-- Prove2me | solution 1 for Formalism.L2.Th1.B.cube_par_subst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T09:47:59.76034+00:00
-- url     : https://prove2.me/submissions/0f8691b8-4ed2-4667-8591-4654cbbf308d

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementB
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ConstantCoeffSubstOfZero
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_LogarithmEquivalence
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_ConstantCoeffEqZeroOfParallelogram
import Theorems.Thm_Formalism_L2_Th1_B_subst_at_variable_one_eq
import Theorems.Thm_Formalism_L2_Th1_B_constantCoeff_subst_two_variables
import Theorems.Thm_Formalism_L2_Th1_B_constantCoeff_subst_one_variable
import Theorems.Thm_Formalism_G_LogP_hs2
import Theorems.Thm_Formalism_G_LogP_psubst_injective
import Theorems.Thm_Formalism_G_LogP_psubst_subst
import Theorems.Thm_Formalism_G_LogP_subst2_subst
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_equivalence_rules
import Theorems.Thm_P2M_Formalism_G_LogP_subst_zero__b4a287294211


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.B
open Formalism.DworkPowerSeriesWeights (Integral)
open Formalism.InvariantFactorPaths.G7 (Simeq at1 cob d1 in3 swap2 DivAB equivalence_rules)
open Formalism.G.LogP (hs2 subst2_subst psubst_subst psubst_injective subst_zero')
variable {K : Type} [Field K] [CharZero K] {ι : Type}
namespace Formalism.L2.Th1.B
theorem _root_.solution (F : MvPowerSeries (Fin 2) K) (hF : MvPowerSeries.constantCoeff F = 0)
    (i f : PowerSeries K) (hi : PowerSeries.constantCoeff i = 0) (U V : MvPowerSeries ι K)
    (hU : MvPowerSeries.constantCoeff U = 0) (hV : MvPowerSeries.constantCoeff V = 0) :
    MvPowerSeries.subst ![U, V] (par F i f) =
      PowerSeries.subst (MvPowerSeries.subst ![U, V] F) f +
        PowerSeries.subst (MvPowerSeries.subst ![U, PowerSeries.subst V i] F) f -
        2 * PowerSeries.subst U f - 2 * PowerSeries.subst V f := by
  have hb := hs2 hU hV
  have h1 : MvPowerSeries.constantCoeff (at1 (1 : Fin 2) i) = 0 := constantCoeff_subst_one_variable i hi _ (by simp)
  have hFI : MvPowerSeries.constantCoeff (FI F i) = 0 := constantCoeff_subst_two_variables F hF _ _ (by simp) h1
  unfold par
  rw [← MvPowerSeries.coe_substAlgHom hb, map_sub, map_sub, map_add, map_mul, map_mul, map_ofNat,
    MvPowerSeries.coe_substAlgHom hb, psubst_subst f hF hb, psubst_subst f hFI hb,
    subst_at_variable_one_eq f 0 hb, subst_at_variable_one_eq f 1 hb]
  unfold FI
  rw [subst2_subst F (by simp) h1 hb, MvPowerSeries.subst_X hb, subst_at_variable_one_eq i 1 hb]
  rfl
end Formalism.L2.Th1.B
