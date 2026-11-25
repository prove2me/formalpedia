-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.DeficitSplitLemmas.orders_bucket_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:14:26.308992+00:00
-- url     : https://prove2.me/submissions/30caee33-b5b4-4780-935c-cc661c1c4dbb

import Definitions.Def_Formalism_SizeWindowBrackets_SecondKindBucket
import Definitions.Def_Formalism_LogFactorialBounds_LogFactorialProofs_PrimeSum
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_RankGapDecayHypothesis
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_PmModulusFacts
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_FourNotDvdOddSqAddOne
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_AdmissibleSchurLemma
import Theorems.Thm_Formalism_RankGapBounds_LocalQuadraticParts_ordersSumY_of
import Theorems.Thm_Formalism_RankGapBounds_LocalQuadraticParts_powTwoPowEqOneIff_holds


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.DeficitSplitLemmas
open Finset Classical
noncomputable section
namespace Formalism.LFunctionChainParameters.DeficitSplitLemmas
theorem _root_.solution : OrdersBucket := by
  obtain ⟨C, hC⟩ := Formalism.RankGapBounds.LocalQuadraticParts.ordersSumY_of Formalism.RankGapBounds.LocalQuadraticParts.powTwoPowEqOneIff_holds
  refine ⟨C, ?_⟩
  intro e J Y mTa s he hJ hY hm hs
  rw [← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left (hC e J Y s he hJ hY hs) (by linarith)
end Formalism.LFunctionChainParameters.DeficitSplitLemmas
