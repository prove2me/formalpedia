-- Prove2me | solution 1 for Formalism.L2.Th1.D.B4.subst_C_mul_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:28:42.800005+00:00
-- url     : https://prove2.me/submissions/58624098-7cc8-4b91-b9e5-e61d4f094d24

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
open B4
open Formalism.L2.Th1.D.B4
variable {K : Type} [Field K] {τ τ' : Type}
namespace Formalism.L2.Th1.D.B4
theorem _root_.solution {a : τ → MvPowerSeries τ' K} (ha : HasSubst a) (c : K) {α : Type}
    (s : Finset α) (f : α → MvPowerSeries τ K) :
    subst a (MvPowerSeries.C c * ∑ k ∈ s, f k) = MvPowerSeries.C c * ∑ k ∈ s, subst a (f k) := by
  rw [MvPowerSeries.subst_mul ha, MvPowerSeries.subst_C, ← MvPowerSeries.coe_substAlgHom ha,
    map_sum]
end Formalism.L2.Th1.D.B4
