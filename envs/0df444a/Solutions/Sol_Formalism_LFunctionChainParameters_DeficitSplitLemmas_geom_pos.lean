-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.DeficitSplitLemmas.geom_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:27:25.285809+00:00
-- url     : https://prove2.me/submissions/65f00dea-d434-412c-9c63-e813d5746ce1

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
theorem _root_.solution (I : Finset ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq : q < 1) (hI : ∀ i ∈ I, 1 ≤ i) :
    ∑ i ∈ I, q ^ i ≤ q / (1 - q) := by
  have hsub : I ⊆ Finset.Ico 1 (I.sup id + 1) := by
    intro i hi
    have : i ≤ I.sup id := Finset.le_sup (f := id) hi
    exact Finset.mem_Ico.2 ⟨hI i hi, by omega⟩
  have h1 : ∑ i ∈ I, q ^ i ≤ ∑ i ∈ Finset.Ico 1 (I.sup id + 1), q ^ i :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => pow_nonneg hq0 i)
  have := geom_sum_Ico_le_of_lt_one (x := q) (m := 1) (n := I.sup id + 1) hq0 hq
  rw [pow_one] at this
  exact h1.trans this
end Formalism.LFunctionChainParameters.DeficitSplitLemmas
