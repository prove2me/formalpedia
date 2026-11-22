-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.slopeLatticeData.mem_idealSmul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:06:37.578787+00:00
-- url     : https://prove2.me/submissions/d8cff30b-eff2-4197-9c87-437065ded4c0

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
omit [IsScalarTower (𝓞 K) K V]
namespace Formalism.LFunctionChainParameters.slopeLatticeData
theorem _root_.solution {I : Submodule (𝓞 K) K} {L : Submodule (𝓞 K) V} {a : K} {x : V}
    (ha : a ∈ I) (hx : x ∈ L) : a • x ∈ idealSmul I L :=
  Submodule.subset_span ⟨a, ha, x, hx, rfl⟩
end Formalism.LFunctionChainParameters.slopeLatticeData
