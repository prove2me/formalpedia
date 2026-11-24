-- Prove2me | solution 1 for Formalism.L2.Th1.B.coboundary_rules_hold
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:40:56.998567+00:00
-- url     : https://prove2.me/submissions/e5f7ea08-847e-4b61-b04d-182c528c78ec

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementB
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ConstantCoeffSubstOfZero
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_LogarithmEquivalence
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_IntegralInverse
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_ConstantCoeffSeriesAtVariable
import Theorems.Thm_Formalism_L2_Th1_B_law_cob_subst
import Theorems.Thm_Formalism_L2_Th1_B_law_coeff_axis0
import Theorems.Thm_Formalism_L2_Th1_B_law_coeff_axis1
import Theorems.Thm_Formalism_L2_Th1_B_law_subst_zero
import Theorems.Thm_Formalism_L2_Th1_B_law_right_zero
import Theorems.Thm_Formalism_L2_Th1_B_law_left_zero
import Theorems.Thm_Formalism_L2_Th1_B_law_comm
import Theorems.Thm_Formalism_G_LogP_hX0
import Theorems.Thm_Formalism_G_LogP_hX1
import Theorems.Thm_Formalism_G_LogP_hs2
import Theorems.Thm_Formalism_G_LogP_psubst_injective
import Theorems.Thm_Formalism_G_LogP_psubst_subst
import Theorems.Thm_Formalism_G_LogP_subst2_subst
import Theorems.Thm_Formalism_G_LogP_subst_XX


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
namespace Formalism.L2.Th1.B
theorem _root_.solution : CobRules := by
  intro K _ _ _ F l f h hf
  have hX0 : MvPowerSeries.constantCoeff (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) = 0 := by simp
  have hX1 : MvPowerSeries.constantCoeff (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) = 0 := by simp
  have h00 : MvPowerSeries.constantCoeff (0 : MvPowerSeries (Fin 2) K) = 0 := by simp
  refine ⟨?_, ?_⟩
  · intro n hn
    rcases hn with hn | hn
    · rw [law_coeff_axis1 _ n hn, law_cob_subst F h.1 f _ _ h00 hX1, law_left_zero h _ hX1,
        law_subst_zero f hf]
      simp
    · rw [law_coeff_axis0 _ n hn, law_cob_subst F h.1 f _ _ hX0 h00, law_right_zero h _ hX0,
        law_subst_zero f hf]
      simp
  · unfold swap2
    rw [law_cob_subst F h.1 f _ _ hX1 hX0, law_comm h _ _ hX1 hX0, Formalism.G.LogP.subst_XX]
    unfold cob at1
    ring
end Formalism.L2.Th1.B
