-- Prove2me | solution 1 for Formalism.L2.Th1.D.TraceNormBounds.sim_pair
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:14:44.238861+00:00
-- url     : https://prove2.me/submissions/df790971-5219-4fd1-8839-0f60bfbb34a1

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_NormLeInvOfLtOne
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_CoboundaryCommutesHomomorphism
import Theorems.Thm_Formalism_L2_Th1_D_TraceNormBounds_sim_subst0

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
theorem _root_.solution {τ : Type} {A B : MvPowerSeries τ K} (hA0 : constantCoeff A = 0)
    (hB0 : constantCoeff B = 0) (hA : Integral A) (hB : Integral B)
    {μ : MvPowerSeries (Fin 2) K} (h : Simeq μ 0) : Simeq (subst ![A, B] μ) 0 := sim_subst0 (fun i => by fin_cases i <;> first | exact hA0 | exact hB0)
    (fun i => by fin_cases i <;> first | exact hA | exact hB) h
end Formalism.L2.Th1.D.TraceNormBounds
