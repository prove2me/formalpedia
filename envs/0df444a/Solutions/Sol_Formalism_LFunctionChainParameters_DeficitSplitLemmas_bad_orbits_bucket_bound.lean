-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.DeficitSplitLemmas.bad_orbits_bucket_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:14:22.366967+00:00
-- url     : https://prove2.me/submissions/706f2810-8b75-4e5c-a08a-b7bad4b8f12e

import Definitions.Def_Formalism_SizeWindowBrackets_SecondKindBucket
import Definitions.Def_Formalism_LogFactorialBounds_LogFactorialProofs_PrimeSum
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_RankGapDecayHypothesis
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_PmModulusFacts
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_FourNotDvdOddSqAddOne
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_AdmissibleSchurLemma
import Theorems.Thm_Formalism_RankGapBounds_V4_tops_lemma_sixteen_holds


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
theorem _root_.solution : BadOrbitsBucket := by
  intro α ι _ _ _ δ β m a ω BAD _ hδ0 hδ1 h16 hβ hω hm ha hcond
  obtain ⟨T, hT1, hT2, hT3⟩ :=
    Formalism.RankGapBounds.V4.tops_lemma_sixteen_holds α ι δ β ω BAD hδ0 hδ1 h16 hβ hω hcond
  refine ⟨T, hT1, hT2, ?_⟩
  have hSum : 0 ≤ ∑ p, ω p := Finset.sum_nonneg (fun p _ => hω p)
  have e : ∑ p, 4 * m * a * ω p * ((T.filter fun t => BAD p t T).card : ℝ) =
      4 * m * a * ∑ p, ω p * ((T.filter fun t => BAD p t T).card : ℝ) := by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro p _; ring
  rw [e]
  have h1 := mul_le_mul_of_nonneg_left hT3 (show 0 ≤ 4 * m * a by positivity)
  have h2 : 4 * β * δ * Fintype.card α * ∑ p, ω p ≤ 8 * β * T.card * ∑ p, ω p := by
    apply mul_le_mul_of_nonneg_right _ hSum
    nlinarith
  have h3 := mul_le_mul_of_nonneg_left h2 (show 0 ≤ 4 * m * a by positivity)
  refine h1.trans (h3.trans (le_of_eq ?_))
  ring
end Formalism.LFunctionChainParameters.DeficitSplitLemmas
