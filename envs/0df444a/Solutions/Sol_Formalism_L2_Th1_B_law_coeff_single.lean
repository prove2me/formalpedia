-- Prove2me | solution 1 for Formalism.L2.Th1.B.law_coeff_single
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:40:57.81769+00:00
-- url     : https://prove2.me/submissions/81b783d2-01d3-4391-b242-ffca5076b6c4

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementB
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ConstantCoeffSubstOfZero
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_LogarithmEquivalence
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_IntegralInverse
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_ConstantCoeffSeriesAtVariable
import Theorems.Thm_Formalism_L2_Th1_B_law_coeff_axis0
import Theorems.Thm_Formalism_L2_Th1_B_law_coeff_axis1
import Theorems.Thm_Formalism_L2_Th1_B_law_right_zero
import Theorems.Thm_Formalism_L2_Th1_B_law_left_zero
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
variable {K : Type} [NormedField K] {ι : Type}
namespace Formalism.L2.Th1.B
theorem _root_.solution {F : MvPowerSeries (Fin 2) K} {l : PowerSeries K} (h : LawLog F l)
    (j : Fin 2) : MvPowerSeries.coeff (Finsupp.single j 1) F = 1 := by
  fin_cases j
  · rw [law_coeff_axis0 F _ (by simp), law_right_zero h _ (by simp)]
    simp [MvPowerSeries.coeff_X]
  · rw [law_coeff_axis1 F _ (by simp), law_left_zero h _ (by simp)]
    simp [MvPowerSeries.coeff_X]
end Formalism.L2.Th1.B
