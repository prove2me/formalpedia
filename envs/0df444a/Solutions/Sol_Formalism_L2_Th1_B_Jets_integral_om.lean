-- Prove2me | solution 1 for Formalism.L2.Th1.B.Jets.integral_om
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:48:03.906811+00:00
-- url     : https://prove2.me/submissions/44859741-7974-4186-8ffe-d530c1dc1463

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementB
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_OneAddMulDerivLogSubst
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_EvalSecondZeroAtVariableZero
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ConstantCoeffSubstOfZero
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_LogarithmEquivalence
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_InvariantDerivationSubstLawThree
import Theorems.Thm_Formalism_L2_Th1_B_Jets_ccX
import Theorems.Thm_Formalism_L2_Th1_B_Jets_inv_dz_eq
import Theorems.Thm_Formalism_L2_Th1_B_Jets_integral_pd
import Theorems.Thm_Formalism_L2_Th1_B_Jets_integral_X
import Theorems.Thm_Formalism_L2_Th1_B_Jets_integral_eval_second_zero
import Theorems.Thm_Formalism_G_LogP_constantCoeff_subst_of_zero
import Theorems.Thm_Formalism_G_LogP_hs2
import Theorems.Thm_Formalism_G_LogP_psubst_injective
import Theorems.Thm_Formalism_G_LogP_psubst_subst
import Theorems.Thm_P2M_Formalism_InvariantFactorPaths_G7_LogarithmEquivalence_integral_subst__564f1f6f92b9


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.B Formalism.L2.Th1.B.Jets
open Formalism.DworkPowerSeriesWeights (Integral mvExp)
open Formalism.InvariantFactorPaths.G7 (Simeq at1 cob d1 in3)
open Formalism.G.LogP (hs2 psubst_subst constantCoeff_subst_of_zero psubst_injective)
variable {K : Type} [NormedField K] [IsUltrametricDist K] [CharZero K]
namespace Formalism.L2.Th1.B.Jets
theorem _root_.solution {F : MvPowerSeries (Fin 2) K} {l : PowerSeries K} (h : LawLog F l)
    (j : Fin 3) : Integral (at1 j (dz l)⁻¹) := by
  rw [inv_dz_eq h.1 h.2.2.2.2 h.2.2.1 h.2.2.2.1]
  exact Formalism.InvariantFactorPaths.G7.LogarithmEquivalence.integral_subst'
    (φ := fun _ : Unit => (MvPowerSeries.X j : MvPowerSeries (Fin 3) K))
    (fun _ => ccX j) (fun _ => integral_X j) (integral_eval_second_zero (integral_pd 1 h.2.1))
end Formalism.L2.Th1.B.Jets
