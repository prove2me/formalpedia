-- Prove2me | solution 1 for Formalism.L2.Th1.D.InverseCommuting.sim_symm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:40:07.707882+00:00
-- url     : https://prove2.me/submissions/23750a04-f658-490b-93f8-5eccfcca4737

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
theorem _root_.solution {f g : MvPowerSeries τ K} (h : Simeq f g) : Simeq g f :=
  (Formalism.InvariantFactorPaths.G7.Top.simeqRules K τ).2.1 f g h
end Formalism.L2.Th1.D.InverseCommuting
