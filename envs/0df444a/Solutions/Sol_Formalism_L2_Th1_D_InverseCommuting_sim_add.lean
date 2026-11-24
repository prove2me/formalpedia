-- Prove2me | solution 1 for Formalism.L2.Th1.D.InverseCommuting.sim_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:39:00.47916+00:00
-- url     : https://prove2.me/submissions/3f6bb4a0-f50a-4bd9-bb35-074afd2b01df

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_BiextensionPointsIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_SubstFirstCoboundaryThree
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_EqZeroOfPowEqOne
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FinalS
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_TilInvariantLOf
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_LogarithmEquivalence_simeqRules
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_Top_simeqRules


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
open Formalism.DworkPowerSeriesWeights (Integral mvExp torus)
open Formalism.InvariantFactorPaths.G7 (lgF at1 Simeq UnrOK IsLawOfLog)
open MvPowerSeries
open Formalism.L2.Th1.D.InverseCommuting
variable {K : Type} [NormedField K] [IsUltrametricDist K] [CharZero K] {τ : Type}
namespace Formalism.L2.Th1.D.InverseCommuting
theorem _root_.solution {f g f' g' : MvPowerSeries τ K} (h1 : Simeq f g) (h2 : Simeq f' g') :
    Simeq (f + f') (g + g') :=
  (Formalism.InvariantFactorPaths.G7.Top.simeqRules K τ).2.2.2.1 f g f' g' h1 h2
end Formalism.L2.Th1.D.InverseCommuting
