-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.slopeLatticeData.idealPow_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:14:58.230018+00:00
-- url     : https://prove2.me/submissions/dd72f981-5607-4025-a270-3615cd70a28f

import Definitions.Def_Formalism_SizeWindowBrackets_SlopesHypothesisFinitePlaces
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SizeMu
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_HtGram
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_MuChar
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DualPl
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_WeightedMeanLemmaNeedsDegree
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_ExistsNsmulMem
import Theorems.Thm_Formalism_LFunctionChainParameters_slopeLatticeData_finPl_coe_ne_zero

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
theorem _root_.solution (n : FinPl K →₀ ℤ) : idealPow n ≠ 0 := by
  unfold idealPow Finsupp.prod
  exact Finset.prod_ne_zero_iff.2 fun w _ => zpow_ne_zero _ (finPl_coe_ne_zero w)
end Formalism.LFunctionChainParameters.slopeLatticeData
