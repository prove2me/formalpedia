-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.slopeLatticeData.locLen_subsingleton
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:31:57.710492+00:00
-- url     : https://prove2.me/submissions/b1681cb1-4bb7-4c8a-826d-a61ea4936386

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
theorem _root_.solution (w : Ideal R) [w.IsPrime] (Q : Type) [AddCommGroup Q] [Module R Q]
    [Subsingleton Q] : locLen w Q = 0 :=
  Module.length_eq_zero_iff.2 (IsLocalizedModule.subsingleton_of_subsingleton w.primeCompl
    (LocalizedModule.mkLinearMap w.primeCompl Q))
end Formalism.LFunctionChainParameters.slopeLatticeData
