-- Prove2me | solution 1 for Formalism.L2.Th1.B.Jets.chain
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:49:02.514543+00:00
-- url     : https://prove2.me/submissions/09b041ea-c791-4a31-a0ad-e71c6108e34a

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementB
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_OneAddMulDerivLogSubst
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_EvalSecondZeroAtVariableZero
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ConstantCoeffSubstOfZero
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_LogarithmEquivalence
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_InvariantDerivationSubstLawThree
import Theorems.Thm_Formalism_L2_Th1_B_Jets_invariant_derivation_subst_law_three
import Theorems.Thm_Formalism_L2_Th1_B_Jets_step2
import Theorems.Thm_Formalism_L2_Th1_B_Jets_step1
import Theorems.Thm_Formalism_L2_Th1_B_Jets_step0
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
variable {F : MvPowerSeries (Fin 2) K} {l : PowerSeries K}
namespace Formalism.L2.Th1.B.Jets
theorem _root_.solution (hF : MvPowerSeries.constantCoeff F = 0) (hc : cob F l = 0)
    (h1 : PowerSeries.coeff 1 l = 1) (f : PowerSeries K) (k : ℕ) :
    (Dj l 0)^[k] (Dj l 0 (Dj l 1 (Dj l 2 (d1 F (cob F f))))) =
      PowerSeries.subst (U3 F) ((Dinv l)^[k + 3] f) := by
  have base : Dj l 0 (Dj l 1 (Dj l 2 (d1 F (cob F f)))) =
      PowerSeries.subst (U3 F) ((Dinv l)^[3] f) := by
    rw [step2 hF hc h1 f, step1 hF hc h1, step0 hF hc h1]
    rfl
  induction k with
  | zero => exact base
  | succ k ih =>
    rw [Function.iterate_succ_apply' (Dj l 0), ih, invariant_derivation_subst_law_three hF hc h1]
    congr 1
    rw [show k + 1 + 3 = (k + 3) + 1 by omega]
    exact (Function.iterate_succ_apply' (Dinv l) (k + 3) f).symm
end Formalism.L2.Th1.B.Jets
