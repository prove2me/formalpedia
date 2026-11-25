-- Prove2me | solution 1 for Formalism.L2.Th1.B.Mul.subst_first_coboundary
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:57:10.462922+00:00
-- url     : https://prove2.me/submissions/780146a4-9419-4093-a9b7-e7dff52e7dad

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_FinalB
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementC
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_MultiplicationBiadditiveHolds
import Theorems.Thm_Formalism_G_LogP_hs2
import Theorems.Thm_Formalism_G_LogP_hs3
import Theorems.Thm_Formalism_G_LogP_psubst_subst
import Theorems.Thm_Formalism_G_LogP_subst2_subst
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_equivalence_rules
import Theorems.Thm_Formalism_L2_Th1_B_constantCoeff_subst_two_variables
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
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.B Formalism.L2.Th1.B.Mul
open Formalism.DworkPowerSeriesWeights (Integral)
open Formalism.InvariantFactorPaths.G7 (Simeq at1 cob d1 in3 swap2 DivAB equivalence_rules)
open Formalism.G.LogP (hs2 hs3 subst2_subst psubst_subst subst_zero')
variable {K : Type} [NormedField K] [IsUltrametricDist K] [CharZero K] {ι : Type}
namespace Formalism.L2.Th1.B.Mul
theorem _root_.solution (F be : MvPowerSeries (Fin 2) K) (hF : MvPowerSeries.constantCoeff F = 0)
    (U V W : MvPowerSeries ι K) (hU : MvPowerSeries.constantCoeff U = 0)
    (hV : MvPowerSeries.constantCoeff V = 0) (hW : MvPowerSeries.constantCoeff W = 0) :
    MvPowerSeries.subst ![U, V, W] (d1 F be) =
      MvPowerSeries.subst ![MvPowerSeries.subst ![U, V] F, W] be -
        MvPowerSeries.subst ![U, W] be - MvPowerSeries.subst ![V, W] be := by
  have hb := hs3 hU hV hW
  have c3 : MvPowerSeries.constantCoeff (in3 F) = 0 := constantCoeff_subst_two_variables F hF _ _ (by simp) (by simp)
  unfold d1
  rw [← MvPowerSeries.coe_substAlgHom hb, map_sub, map_sub, MvPowerSeries.coe_substAlgHom hb,
    subst2_subst be c3 (by simp) hb, subst2_subst be (by simp) (by simp) hb,
    subst2_subst be (by simp) (by simp) hb]
  unfold in3
  rw [subst2_subst F (by simp) (by simp) hb, MvPowerSeries.subst_X hb, MvPowerSeries.subst_X hb,
    MvPowerSeries.subst_X hb]
  rfl
end Formalism.L2.Th1.B.Mul
