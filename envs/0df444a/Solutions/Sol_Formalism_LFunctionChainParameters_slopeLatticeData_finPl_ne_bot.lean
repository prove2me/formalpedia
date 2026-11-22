-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.slopeLatticeData.finPl_ne_bot
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:07:01.724278+00:00
-- url     : https://prove2.me/submissions/c0445a8a-0efe-43f1-a4d6-839e90e21510

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
variable {K : Type} [Field K] [NumberField K]
namespace Formalism.LFunctionChainParameters.slopeLatticeData
theorem _root_.solution (w : FinPl K) : w.1 ≠ ⊥ := by
  intro h
  have hm := w.2
  rw [h] at hm
  exact NumberField.RingOfIntegers.not_isField K (Ring.isField_iff_maximal_bot.2 hm)
end Formalism.LFunctionChainParameters.slopeLatticeData
