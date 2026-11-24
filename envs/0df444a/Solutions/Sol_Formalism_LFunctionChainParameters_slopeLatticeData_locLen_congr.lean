-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.slopeLatticeData.locLen_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:30:54.451244+00:00
-- url     : https://prove2.me/submissions/59769cf6-2950-49af-9477-9c6bb0c69ebd

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
variable {R : Type} [CommRing R]
namespace Formalism.LFunctionChainParameters.slopeLatticeData
theorem _root_.solution (w : Ideal R) [w.IsPrime] {M N : Type} [AddCommGroup N] [Module R N]
    [AddCommGroup M] [Module R M] (e : M ≃ₗ[R] N) : locLen w M = locLen w N :=
  le_antisymm
    (Module.length_le_of_injective (LocalizedModule.map w.primeCompl e.toLinearMap)
      (LocalizedModule.map_injective _ _ e.injective))
    (Module.length_le_of_injective (LocalizedModule.map w.primeCompl e.symm.toLinearMap)
      (LocalizedModule.map_injective _ _ e.symm.injective))
end Formalism.LFunctionChainParameters.slopeLatticeData
