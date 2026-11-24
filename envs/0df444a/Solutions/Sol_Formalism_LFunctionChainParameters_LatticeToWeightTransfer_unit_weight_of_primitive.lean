-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LatticeToWeightTransfer.unit_weight_of_primitive
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:32:26.823159+00:00
-- url     : https://prove2.me/submissions/157820d5-a68d-42c2-995f-1da027f74fdb

import Definitions.Def_Formalism_SizeWindowBrackets_SlopeHypothesesRounded
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_WeightedSlopeExcessDecomposition
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_LevelOfCongruence
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_JointDModelAppliesUnitLattice
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_ExistsNsmulMem
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_SlopeInequalityOfLattices
import Theorems.Thm_Formalism_LFunctionChainParameters_LatticeToWeightTransfer_unit_weight_transfer
import Theorems.Thm_Formalism_LFunctionChainParameters_LatticeToWeightTransfer_primitive_transfer
import Theorems.Thm_Formalism_LFunctionChainParameters_LatticeToWeightTransfer_primitive_transfer_sizes

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
theorem _root_.solution : QuotientSlopeBoundsOfPrimitiveData D C Xpp cT Q := by
  intro hH hI hS
  exact unit_weight_transfer D C Xpp (toP D Q) (primitive_transfer D Q hH) hI
    (primitive_transfer_sizes D C Xpp cT Q (fun u0 u => (hH u0 u).2.2.1) hS)
end Formalism.LFunctionChainParameters.LatticeToWeightTransfer
