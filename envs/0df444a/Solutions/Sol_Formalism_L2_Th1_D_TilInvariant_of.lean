-- Prove2me | solution 1 for Formalism.L2.Th1.D.TilInvariant_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:13:35.381246+00:00
-- url     : https://prove2.me/submissions/52659fa7-4383-43ef-8005-38541691b3f1

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_BiextensionPointsIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_SubstFirstCoboundaryThree
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_EqZeroOfPowEqOne
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FinalS
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_TilInvariantLOf

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
open InverseCommuting
namespace Formalism.L2.Th1.D
theorem _root_.solution : TilInvariantL → LetterShift → TilInvariant := by
  intro hTI hLS K _ _ _ l d _ σ hU hd2 hd F hF be0 hF1 hF2 ι _ _ om oms hOw hT u hu
  exact hTI K l d σ hU hd2 hd F hF be0 hF1 hF2 ι om oms hOw hT u hu (ZMod d) (letLog l)
    (hLS K l d σ hU.1).2.1
end Formalism.L2.Th1.D
