-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.DeficitSplitLemmas.sigma_mean_variance
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:14:31.755113+00:00
-- url     : https://prove2.me/submissions/5da930a9-95b9-4192-b3e5-2b53d6dac551

import Definitions.Def_Formalism_SizeWindowBrackets_SecondKindBucket
import Definitions.Def_Formalism_LogFactorialBounds_LogFactorialProofs_PrimeSum
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_RankGapDecayHypothesis
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_PmModulusFacts
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_FourNotDvdOddSqAddOne
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_AdmissibleSchurLemma
import Theorems.Thm_Formalism_LFunctionChainParameters_DeficitSplitLemmas_sigma_mean

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
theorem _root_.solution : SigMeanVar := by
  intro Ω ν _ π V Vo kap N m T c hm hc hπ hsub hkap hmean hN
  refine le_trans ?_ (sigma_mean Ω ν π V kap N m T c hm hc hmean hN)
  apply Finset.sum_le_sum
  intro o _
  apply mul_le_mul_of_nonneg_left _ (hπ o)
  apply mul_le_mul_of_nonneg_left _ hm
  exact Finset.sum_le_sum_of_subset_of_nonneg (hsub o) (fun v hv _ => hkap v hv o)
end Formalism.LFunctionChainParameters.DeficitSplitLemmas
