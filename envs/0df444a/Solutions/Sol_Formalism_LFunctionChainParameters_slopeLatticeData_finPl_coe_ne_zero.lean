-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.slopeLatticeData.finPl_coe_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:12:22.151165+00:00
-- url     : https://prove2.me/submissions/4f9c31af-f764-4632-86c2-07b40816535c

import Definitions.Def_Formalism_SizeWindowBrackets_SlopesHypothesisFinitePlaces
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SizeMu
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_HtGram
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_MuChar
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DualPl
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_WeightedMeanLemmaNeedsDegree
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_ExistsNsmulMem
import Theorems.Thm_Formalism_LFunctionChainParameters_slopeLatticeData_finPl_ne_bot

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
theorem _root_.solution (w : FinPl K) :
    (w.1 : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) ≠ 0 :=
  FractionalIdeal.coeIdeal_ne_zero.2 (finPl_ne_bot w)
end Formalism.LFunctionChainParameters.slopeLatticeData
