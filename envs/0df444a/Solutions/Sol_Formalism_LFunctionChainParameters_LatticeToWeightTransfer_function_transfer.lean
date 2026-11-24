-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LatticeToWeightTransfer.function_transfer
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:29:31.082618+00:00
-- url     : https://prove2.me/submissions/f8987041-8cc7-4492-88a4-d18abbfc92fb

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
variable (D : Data U0 W Top m f) (C : Consts)
namespace Formalism.LFunctionChainParameters.LatticeToWeightTransfer
theorem _root_.solution : BridgeF D := by
  have e : ∀ a b : ℝ, 4 * a * b = 4 * (a * b) := fun a b => mul_assoc 4 a b
  unfold BridgeF Data.SlopeIneq SideF ConclFAt PhiMonotonicityLemmas.ConclF PhiMonotonicityLemmas.ErrF PhiMonotonicityLemmas.phi
  constructor
  · rintro h u0 ⟨h1, h2, h3, h4, h5, h6, h7⟩
    have := h u0 h1 h2 h3 h4 h5 h6 h7
    rwa [e] at this
  · intro h u0 h1 h2 h3 h4 h5 h6 h7
    have := h u0 ⟨h1, h2, h3, h4, h5, h6, h7⟩
    rwa [e]
end Formalism.LFunctionChainParameters.LatticeToWeightTransfer
