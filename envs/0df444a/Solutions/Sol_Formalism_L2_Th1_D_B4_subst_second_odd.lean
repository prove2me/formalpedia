-- Prove2me | solution 1 for Formalism.L2.Th1.D.B4.subst_second_odd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:41:39.731723+00:00
-- url     : https://prove2.me/submissions/9a2d936a-878b-4ca7-bc8b-06b930aac0d4

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
theorem _root_.solution (ha : HasSubst a) {s : ZMod d} (hs : ¬ s.val % 2 = 0) :
    subst a (s2 (K := K) s) = a (false, s) := by
  unfold s2
  rw [if_neg hs, MvPowerSeries.subst_X ha]
end Formalism.L2.Th1.D.B4
