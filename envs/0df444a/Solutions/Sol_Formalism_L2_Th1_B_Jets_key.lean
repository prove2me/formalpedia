-- Prove2me | solution 1 for Formalism.L2.Th1.B.Jets.key
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:47:52.740919+00:00
-- url     : https://prove2.me/submissions/8b2db9fb-c289-4413-adad-13f4f8bd10c8

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementB
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_OneAddMulDerivLogSubst
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_EvalSecondZeroAtVariableZero
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ConstantCoeffSubstOfZero
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_LogarithmEquivalence
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_InvariantDerivationSubstLawThree
import Theorems.Thm_Formalism_L2_Th1_B_Jets_ccX
import Theorems.Thm_Formalism_L2_Th1_B_Jets_inv_mul_dz_subst
import Theorems.Thm_Formalism_G_LogCR_pderiv_psubst
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
theorem _root_.solution {l : PowerSeries K} (h1 : PowerSeries.coeff 1 l = 1) (j k : Fin 3) :
    at1 j (dz l)⁻¹ * pd j (PowerSeries.subst (MvPowerSeries.X k : MvPowerSeries (Fin 3) K) l) =
      if k = j then 1 else 0 := by
  have hX : MvPowerSeries.constantCoeff (MvPowerSeries.X k : MvPowerSeries (Fin 3) K) = 0 := ccX k
  simp only [pd]
  rw [Formalism.G.LogCR.pderiv_psubst hX]
  by_cases hkj : k = j
  · subst hkj
    rw [MvPowerSeries.pderiv_X_self, mul_one, if_pos rfl]
    exact inv_mul_dz_subst h1 hX
  · rw [MvPowerSeries.pderiv_X_of_ne hkj, mul_zero, mul_zero, if_neg hkj]
end Formalism.L2.Th1.B.Jets
