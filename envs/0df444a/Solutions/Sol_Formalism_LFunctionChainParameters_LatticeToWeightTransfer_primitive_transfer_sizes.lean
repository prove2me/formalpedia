-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LatticeToWeightTransfer.primitive_transfer_sizes
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:29:31.661693+00:00
-- url     : https://prove2.me/submissions/4d538419-454e-4475-a8a5-d214e4c15f52

import Definitions.Def_Formalism_SizeWindowBrackets_SlopeHypothesesRounded
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_WeightedSlopeExcessDecomposition
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_LevelOfCongruence
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_JointDModelAppliesUnitLattice
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_ExistsNsmulMem
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_SlopeInequalityOfLattices

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField Matrix
open Formalism.CorankShareLayerCake.FR Formalism.HN
noncomputable section
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.LatticeToWeightTransfer
open Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds
variable {U0 : Type} [Fintype U0] {W : U0 → Type} [∀ u0, Fintype (W u0)]
  [∀ u0, Nonempty (W u0)] {Top : Type} [Fintype Top] {m f : ℕ}
variable {ι : Type} [DecidableEq ι]
variable (D : Data U0 W Top m f) (C : Consts) (Xpp cT : ℝ) (Q : ∀ u0, W u0 → PPrim ι m)
namespace Formalism.LFunctionChainParameters.LatticeToWeightTransfer
theorem _root_.solution : BridgePrimSizes D C Xpp cT Q := by
  intro hT h
  obtain ⟨h4, hcT, hB, hab, hsz⟩ := h
  refine ⟨h4, hB, fun u0 u => ?_⟩
  obtain ⟨hIO, hlam, hRd⟩ := hsz u0 u
  refine ⟨hIO, ?_, hRd⟩
  have hlog : 0 ≤ Real.log (D.T u0 u) := Real.log_nonneg (by linarith [hT u0 u])
  have hX : 0 ≤ D.nT * (m : ℝ) * (D.a / D.k + D.b') :=
    mul_nonneg (mul_nonneg (by unfold Data.nT; positivity) (by positivity)) hab
  have h1 : 4 * (Q u0 u).lam ≤ C.cSl1 * D.nT * (m : ℝ) * (D.a / D.k + D.b') := by
    have := mul_le_mul_of_nonneg_right hcT hX
    nlinarith
  exact mul_le_mul_of_nonneg_right h1 hlog
end Formalism.LFunctionChainParameters.LatticeToWeightTransfer
