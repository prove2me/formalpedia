-- Prove2me | solution 1 for Formalism.L2.Th1.D.B4.subst_first_coordinate
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:28:36.40067+00:00
-- url     : https://prove2.me/submissions/2f61352a-0e24-42f0-bd6a-b18b66993254

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_LetterShift
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FinalS
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_Transfer
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_BiextensionHypothesesOfConditions

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
open Formalism.DworkPowerSeriesWeights (Integral mvExp torus BHyp NoLowBidegree letterLog de1 de2 s0 s1 s2 s1' s2' V2 degE)
open Formalism.InvariantFactorPaths.G7 (Simeq DivAB UnrOK IsLawOfLog)
open MvPowerSeries (subst HasSubst constantCoeff)
open Formalism.L2.Th1.D.B4
variable {K : Type} [Field K] {τ : Type} {d : ℕ} {a : V2 d → MvPowerSeries τ K}
namespace Formalism.L2.Th1.D.B4
theorem _root_.solution (ha : HasSubst a) (s : ZMod d) : subst a (s0 (K := K) s) = a (false, s) :=
  MvPowerSeries.subst_X ha _
end Formalism.L2.Th1.D.B4
