-- Prove2me | solution 1 for Formalism.L2.Th1.D.Pair.constantCoeff_inVar_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:37:28.93426+00:00
-- url     : https://prove2.me/submissions/ec6f8b71-6a8f-49f7-b49f-f206bf46c096

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_LetterShift
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FinalS
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_SubstFirstCoboundaryThree

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
open Formalism.InvariantFactorPaths.G7 (lgF at1 Simeq DivAB d1 swap2 in3 cob UnrOK IsLawOfLog SimeqRules)
open MvPowerSeries
open Formalism.L2.Th1.D.Pair
variable {K : Type} [Field K]
namespace Formalism.L2.Th1.D.Pair
theorem _root_.solution {ι : Type} (x : ι) {f : PowerSeries K}
    (hf : PowerSeries.constantCoeff f = 0) : constantCoeff (at1 x f) = 0 := by
  unfold at1
  exact PowerSeries.constantCoeff_subst_eq_zero (a := (X x : MvPowerSeries ι K)) (by simp) f hf
end Formalism.L2.Th1.D.Pair
