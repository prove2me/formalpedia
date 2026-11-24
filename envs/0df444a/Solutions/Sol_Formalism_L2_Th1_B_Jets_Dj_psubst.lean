-- Prove2me | solution 1 for Formalism.L2.Th1.B.Jets.Dj_psubst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:48:01.301282+00:00
-- url     : https://prove2.me/submissions/777d1356-ab63-412c-b297-dc4ea72e7344

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementB
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_OneAddMulDerivLogSubst
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_EvalSecondZeroAtVariableZero
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ConstantCoeffSubstOfZero
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_LogarithmEquivalence
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_InvariantDerivationSubstLawThree
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
theorem _root_.solution {l : PowerSeries K} (h1 : PowerSeries.coeff 1 l = 1) (j : Fin 3)
    (g : PowerSeries K) {U : MvPowerSeries (Fin 3) K} (hU : MvPowerSeries.constantCoeff U = 0) :
    Dj l j (PowerSeries.subst U g) =
      PowerSeries.subst U (Dinv l g) * (at1 j (dz l)⁻¹ * pd j (PowerSeries.subst U l)) := by
  have hinv := inv_mul_dz_subst h1 hU
  simp only [dz] at hinv
  simp only [Dj, pd, Dinv, dz]
  rw [Formalism.G.LogCR.pderiv_psubst hU, Formalism.G.LogCR.pderiv_psubst hU,
    PowerSeries.subst_mul (PowerSeries.HasSubst.of_constantCoeff_zero hU)]
  linear_combination (-(at1 j (PowerSeries.derivative K l)⁻¹ *
    PowerSeries.subst U (PowerSeries.derivative K g) * MvPowerSeries.pderiv K j U)) * hinv
end Formalism.L2.Th1.B.Jets
