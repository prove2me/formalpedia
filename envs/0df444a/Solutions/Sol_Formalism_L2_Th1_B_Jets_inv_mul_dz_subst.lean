-- Prove2me | solution 1 for Formalism.L2.Th1.B.Jets.inv_mul_dz_subst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:33:29.796135+00:00
-- url     : https://prove2.me/submissions/f2db7ed3-4891-4b69-ae55-f57dfa7d64bf

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementB
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_OneAddMulDerivLogSubst
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_EvalSecondZeroAtVariableZero
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ConstantCoeffSubstOfZero
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_LogarithmEquivalence
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_InvariantDerivationSubstLawThree
import Theorems.Thm_Formalism_L2_Th1_B_Jets_inv_mul_dz
import Theorems.Thm_Formalism_G_LogP_constantCoeff_subst_of_zero
import Theorems.Thm_Formalism_G_LogP_hs2
import Theorems.Thm_Formalism_G_LogP_psubst_injective
import Theorems.Thm_Formalism_G_LogP_psubst_subst


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
variable {K : Type} [Field K] [CharZero K]
namespace Formalism.L2.Th1.B.Jets
theorem _root_.solution {ι : Type} {l : PowerSeries K} (h1 : PowerSeries.coeff 1 l = 1)
    {U : MvPowerSeries ι K} (hU : MvPowerSeries.constantCoeff U = 0) :
    PowerSeries.subst U (dz l)⁻¹ * PowerSeries.subst U (dz l) = 1 := by
  have hs : PowerSeries.HasSubst U := PowerSeries.HasSubst.of_constantCoeff_zero hU
  rw [← PowerSeries.coe_substAlgHom hs, ← map_mul, inv_mul_dz h1, map_one]
end Formalism.L2.Th1.B.Jets
