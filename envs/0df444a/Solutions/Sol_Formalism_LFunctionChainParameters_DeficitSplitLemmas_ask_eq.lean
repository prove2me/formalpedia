-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.DeficitSplitLemmas.ask_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:27:19.023143+00:00
-- url     : https://prove2.me/submissions/643455d6-c118-4708-8182-a78ebfaa924d

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
theorem _root_.solution {κ τ : Type*} (Ps : Finset ℕ) (J : Finset κ) (TT : Finset τ)
    (vonMangoldtClassSum : κ → τ → ℕ → ℝ) (dT : κ → τ → ℝ) :
    ASK Ps J TT vonMangoldtClassSum dT = (∑ p ∈ Ps, 2 * Real.log p * ∑ j ∈ J, ∑ t ∈ TT, vonMangoldtClassSum j t p) +
      ∑ j ∈ J, ∑ t ∈ TT, dT j t := by
  unfold ASK
  simp only [Finset.sum_add_distrib, Finset.mul_sum]
  congr 1
  rw [Finset.sum_congr rfl (fun j _ => Finset.sum_comm)]
  exact Finset.sum_comm
end Formalism.LFunctionChainParameters.DeficitSplitLemmas
