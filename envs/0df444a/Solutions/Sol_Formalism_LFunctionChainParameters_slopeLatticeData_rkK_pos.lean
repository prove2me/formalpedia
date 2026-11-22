-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.slopeLatticeData.rkK_pos
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:05:53.054036+00:00
-- url     : https://prove2.me/submissions/2fccf4f8-c63e-48f6-b134-b45ff5ba9bce

import Definitions.Def_Formalism_SizeWindowBrackets_SlopesHypothesisFinitePlaces
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SizeMu
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_HtGram
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_MuChar
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DualPl
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_WeightedMeanLemmaNeedsDegree
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_ExistsNsmulMem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField
noncomputable section
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.slopeLatticeData
open Formalism.HN Formalism.HermitianLatticesTheory
variable {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
namespace Formalism.LFunctionChainParameters.slopeLatticeData
theorem _root_.solution [FiniteDimensional K V] {L : Submodule (𝓞 K) V} (hL : L ≠ ⊥) : 0 < rkK L := by
  unfold rkK
  rw [Nat.pos_iff_ne_zero, Ne, Submodule.finrank_eq_zero]
  intro h
  apply hL
  rw [eq_bot_iff]
  intro x hx
  have : x ∈ Submodule.span K (L : Set V) := Submodule.subset_span hx
  rw [h] at this
  exact this
end Formalism.LFunctionChainParameters.slopeLatticeData
