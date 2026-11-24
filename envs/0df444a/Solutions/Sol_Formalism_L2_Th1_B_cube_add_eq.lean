-- Prove2me | solution 1 for Formalism.L2.Th1.B.cube_add_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:13:27.31385+00:00
-- url     : https://prove2.me/submissions/414fb842-98b3-45a9-a894-5093b4d6cd3b

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementB
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ConstantCoeffSubstOfZero
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_LogarithmEquivalence
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_ConstantCoeffEqZeroOfParallelogram
import Theorems.Thm_Formalism_L2_Th1_B_constantCoeff_subst_two_variables
import Theorems.Thm_Formalism_L2_Th1_B_cube_log_add
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
variable {K : Type} [NormedField K] [CharZero K] {ι : Type}
namespace Formalism.L2.Th1.B
theorem _root_.solution {F : MvPowerSeries (Fin 2) K} {l : PowerSeries K} (h : LawLog F l)
    (U V W : MvPowerSeries ι K) (hU : MvPowerSeries.constantCoeff U = 0)
    (hV : MvPowerSeries.constantCoeff V = 0) (hW : MvPowerSeries.constantCoeff W = 0)
    (e : PowerSeries.subst U l + PowerSeries.subst V l = PowerSeries.subst W l) :
    MvPowerSeries.subst ![U, V] F = W :=
  psubst_injective h.2.2.1 h.2.2.2.1 (constantCoeff_subst_two_variables F h.1 U V hU hV) hW
    ((cube_log_add h U V hU hV).trans e)
end Formalism.L2.Th1.B
