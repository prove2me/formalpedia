-- Prove2me | solution 1 for Formalism.L2.Th1.D.TraceNormBounds.integral_law_first_two_of_three
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:59:44.368607+00:00
-- url     : https://prove2.me/submissions/a34f5274-b281-4667-b876-4ae4f71f8ca5

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_NormLeInvOfLtOne
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_CoboundaryCommutesHomomorphism
import Theorems.Thm_Formalism_FG_FormalGroupCoefficients_integral_X
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_FrobeniusSubstitution_integral_X
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_GramFrameCompositionLinFacts_integral_X
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoS_integral_X
import Theorems.Thm_Formalism_L2_Th1_D_FormalExponential_integral_X
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
open scoped BigOperators
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.D
open Formalism.DworkPowerSeriesWeights (Integral mvExp)
open Formalism.InvariantFactorPaths.G7 (lgF at1 Simeq DivAB d1 swap2 in3 cob UnrOK IsLawOfLog frobVar)
open MvPowerSeries
open Formalism.L2.Th1.D.TraceNormBounds
variable {K : Type} [NormedField K] [IsUltrametricDist K] [CharZero K]
namespace Formalism.L2.Th1.D.TraceNormBounds
theorem _root_.solution {F : MvPowerSeries (Fin 2) K} (hF : Integral F) : Integral (in3 F) := by
  unfold in3
  exact Formalism.InvariantFactorPaths.G7.LogarithmEquivalence.integral_subst' (by intro i; fin_cases i <;> simp)
    (by intro i; fin_cases i <;> exact Formalism.InvariantFactorPaths.G7.TwoS.integral_X _) hF
end Formalism.L2.Th1.D.TraceNormBounds
