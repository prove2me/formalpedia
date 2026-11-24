-- Prove2me | solution 1 for Formalism.L2.Th1.D.B4.linOL_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:28:35.790385+00:00
-- url     : https://prove2.me/submissions/a3cdea48-e283-44ed-b191-22627d560274

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
variable {K : Type} [NormedField K] {τ : Type} {d : ℕ} [NeZero d]
namespace Formalism.L2.Th1.D.B4
theorem _root_.solution (σ : K →+* K) (c : K) {L L' : ZMod d → MvPowerSeries τ K}
    (h : ∀ s : ZMod d, ¬ s.val % 2 = 0 → L s = L' s) : linOL σ c L = linOL σ c L' := by
  unfold linOL
  refine Finset.sum_congr rfl fun s _ => ?_
  split_ifs with hs
  · rfl
  · rw [h s hs]
end Formalism.L2.Th1.D.B4
