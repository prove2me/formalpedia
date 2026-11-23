-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.DeficitSplitLemmas.deficit_dropped
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:34:51.336967+00:00
-- url     : https://prove2.me/submissions/1d9ae1ee-2381-4829-9304-3bdcff30b03c

import Definitions.Def_Formalism_SizeWindowBrackets_SecondKindBucket
import Definitions.Def_Formalism_LogFactorialBounds_LogFactorialProofs_PrimeSum
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_RankGapDecayHypothesis
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_PmModulusFacts
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_FourNotDvdOddSqAddOne
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_AdmissibleSchurLemma

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
theorem _root_.solution {κ τ : Type*} (J : Finset κ) (TT : Finset τ) (vonMangoldtClassSum : κ → τ → ℕ → ℝ)
    (gain : κ → ℕ → ℝ) (tau : ℕ → ℝ) (p : ℕ) (hg : ∀ j ∈ J, gain j p = 0) (ht : tau p = 0) :
    deficit J TT vonMangoldtClassSum gain tau p = wholeAsk J TT vonMangoldtClassSum p := by
  unfold deficit wholeAsk
  rw [Finset.sum_eq_zero hg, ht]; ring
end Formalism.LFunctionChainParameters.DeficitSplitLemmas
