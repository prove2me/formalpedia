-- Prove2me | solution 1 for Formalism.L2.Th1.D.theta_integer_is_s_substitution
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T06:56:57.620832+00:00
-- url     : https://prove2.me/submissions/aa476230-a44c-4380-b5d1-233563cf07bf

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_BiextensionHypothesesOfLevelOne
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_ThetaInZIsThetaLog
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_StatementC
import Definitions.Def_Formalism_GaussJetBounds_ThmAEntryFull
import Definitions.Def_Formalism_GaussJetBounds_OneLetterGauss
import Definitions.Def_Formalism_GaussJetBounds_ThmAGauss
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_ThetaLogIsSubst
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FinalS
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_ThetaIntegerIsSSubstitution
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.D
open Formalism.DworkPowerSeriesWeights (Integral mvExp torus BHyp Unram entLog oneLog thetaZ thetaOne frameJet frameJetOne
  nablaO)
open Formalism.InvariantFactorPaths.G7 (lgF at1 Simeq DivAB d1 swap2 UnrOK IsLawOfLog BetaHyp OmOK lamF thetaLog sSub zLin)
namespace Formalism.L2.Th1.D
theorem _root_.solution : ThetaInZIsSSub := by
  intro K0 K _ _ l ν r0 r1 _ σ j om oms Tht
  unfold thetaInZ
  congr 1
  funext x
  unfold xOfZ Formalism.InvariantFactorPaths.G7.sSub Formalism.InvariantFactorPaths.G7.zLin conjJ
  congr 1
  by_cases h : x.1 = false
  · simp only [h, if_true]
  · simp only [h]
    refine Finset.sum_congr rfl fun s _ => ?_
    rcases Nat.mod_two_eq_zero_or_one s.val with h2 | h2 <;> simp [h2]
end Formalism.L2.Th1.D
