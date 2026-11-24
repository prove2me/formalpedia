-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LatticeToWeightTransfer.exponent_transfer
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:29:30.463735+00:00
-- url     : https://prove2.me/submissions/bd1209e6-7464-4e0a-ba86-cda658b033b6

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
variable (D : Data U0 W Top m f) (C : Consts) (Xpp : ℝ) (P : ∀ u0, W u0 → PData ι m)
namespace Formalism.LFunctionChainParameters.LatticeToWeightTransfer
theorem _root_.solution : BridgeEe D P := by
  intro hI u0 u
  unfold Data.Ee PData.Ee UnitWeightPartition.Ee
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => (hI u0 u).2.2 j
end Formalism.LFunctionChainParameters.LatticeToWeightTransfer
