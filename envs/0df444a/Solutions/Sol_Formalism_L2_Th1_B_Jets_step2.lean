-- Prove2me | solution 1 for Formalism.L2.Th1.B.Jets.step2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:28:55.856266+00:00
-- url     : https://prove2.me/submissions/d594c3cf-1fdb-4f57-b601-99c9184557e0

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementB
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_OneAddMulDerivLogSubst
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_EvalSecondZeroAtVariableZero
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ConstantCoeffSubstOfZero
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_LogarithmEquivalence
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_InvariantDerivationSubstLawThree
import Theorems.Thm_Formalism_L2_Th1_B_Jets_Dj_sub
import Theorems.Thm_Formalism_L2_Th1_B_Jets_coboundary_formal_add_biextension
import Theorems.Thm_Formalism_L2_Th1_B_Jets_Dj_X
import Theorems.Thm_Formalism_L2_Th1_B_Jets_invariant_derivation_subst_law_pair
import Theorems.Thm_Formalism_L2_Th1_B_Jets_invariant_derivation_subst_law_three
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
    (h1 : PowerSeries.coeff 1 l = 1) (f : PowerSeries K) :
    Dj l 2 (d1 F (cob F f)) =
      PowerSeries.subst (U3 F) (Dinv l f) - PowerSeries.subst (U2 F 0 2) (Dinv l f) -
        (PowerSeries.subst (U2 F 1 2) (Dinv l f) -
          PowerSeries.subst (MvPowerSeries.X 2 : MvPowerSeries (Fin 3) K) (Dinv l f)) := by
  rw [coboundary_formal_add_biextension hF f]
  simp only [Dj_sub, invariant_derivation_subst_law_three hF hc h1, Dj_X h1]
  rw [invariant_derivation_subst_law_pair hF hc h1 2 0 1 (by decide), invariant_derivation_subst_law_pair hF hc h1 2 0 2 (by decide),
    invariant_derivation_subst_law_pair hF hc h1 2 1 2 (by decide)]
  simp
end Formalism.L2.Th1.B.Jets
