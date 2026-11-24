-- Prove2me | solution 1 for Formalism.L2.Th1.B.law_cob_subst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:33:34.128558+00:00
-- url     : https://prove2.me/submissions/f2617a24-3d2a-4fe1-8720-08597ca10988

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementB
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ConstantCoeffSubstOfZero
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_LogarithmEquivalence
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_IntegralInverse
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_ConstantCoeffSeriesAtVariable
import Theorems.Thm_Formalism_L2_Th1_B_subst_at_variable_eq_subst
import Theorems.Thm_Formalism_G_LogP_hs2
import Theorems.Thm_Formalism_G_LogP_psubst_injective
import Theorems.Thm_Formalism_G_LogP_psubst_subst
import Theorems.Thm_Formalism_G_LogP_subst2_subst


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
open Formalism.InvariantFactorPaths.G7 (Simeq at1 cob d1 swap2 DivAB)
open Formalism.G.LogP (hs2 subst2_subst psubst_subst psubst_injective)
variable {K : Type} [Field K] {ι : Type}
namespace Formalism.L2.Th1.B
theorem _root_.solution (F : MvPowerSeries (Fin 2) K) (hF : MvPowerSeries.constantCoeff F = 0)
    (f : PowerSeries K) (U V : MvPowerSeries ι K) (hU : MvPowerSeries.constantCoeff U = 0)
    (hV : MvPowerSeries.constantCoeff V = 0) :
    MvPowerSeries.subst ![U, V] (cob F f) =
      PowerSeries.subst (MvPowerSeries.subst ![U, V] F) f - PowerSeries.subst U f -
        PowerSeries.subst V f := by
  have hb := hs2 hU hV
  unfold cob
  rw [← MvPowerSeries.coe_substAlgHom hb, map_sub, map_sub, MvPowerSeries.coe_substAlgHom hb,
    psubst_subst f hF hb, subst_at_variable_eq_subst f 0 hb, subst_at_variable_eq_subst f 1 hb]
  rfl
end Formalism.L2.Th1.B
