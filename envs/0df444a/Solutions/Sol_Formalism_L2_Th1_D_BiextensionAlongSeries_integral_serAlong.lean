-- Prove2me | solution 1 for Formalism.L2.Th1.D.BiextensionAlongSeries.integral_serAlong
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:17:47.883345+00:00
-- url     : https://prove2.me/submissions/41f63a61-7c59-46cf-a9e2-797b2f5c8897

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KurComplete
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_RelativeThetaFactorization
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_BiextensionOfExpSpec
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_BiextensionPointsOfExpSpec
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_BiextensionRelationOfExpSpec
import Theorems.Thm_Formalism_FG_FormalGroupCoefficients_integral_X
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_FormalGroupLawNegation_integral_X
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_FrobeniusSubstitution_integral_X
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_GramFrameCompositionLinFacts_integral_X
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoS_integral_X
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_mvExp_add
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
open Formalism.DworkPowerSeriesWeights (Integral mvExp torus entLog bSum linSub idM ZV serAlong)
open Formalism.InvariantFactorPaths.G7 (lgF at1 Simeq UnrOK IsLawOfLog mvExp_add)
open MvPowerSeries
open Pair
open Formalism.L2.Th1.D.BiextensionAlongSeries
variable {K : Type} [NormedField K]
namespace Formalism.L2.Th1.D.BiextensionAlongSeries
theorem _root_.solution [IsUltrametricDist K] {ι κ : Type} [Finite ι] (e : ι → κ)
    {f : MvPowerSeries ι K} (hf : Integral f) : Integral (serAlong e f) :=
  Formalism.InvariantFactorPaths.G7.LogarithmEquivalence.integral_subst' (fun i => constantCoeff_X (e i))
    (fun i => Formalism.InvariantFactorPaths.G7.TwoS.integral_X (e i)) hf
end Formalism.L2.Th1.D.BiextensionAlongSeries
