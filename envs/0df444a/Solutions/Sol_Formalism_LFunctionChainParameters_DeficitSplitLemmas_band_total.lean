-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.DeficitSplitLemmas.band_total
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:05:23.794894+00:00
-- url     : https://prove2.me/submissions/b00ecd7b-39cf-46f4-8512-ff1cae5db2d1

import Definitions.Def_Formalism_SizeWindowBrackets_SecondKindBucket
import Definitions.Def_Formalism_LogFactorialBounds_LogFactorialProofs_PrimeSum
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_RankGapDecayHypothesis
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_PmModulusFacts
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_FourNotDvdOddSqAddOne
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_AdmissibleSchurLemma
import Theorems.Thm_Formalism_LFunctionChainParameters_DeficitSplitLemmas_band_sum

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
theorem _root_.solution : BandTotal := by
  intro I P X' c p₀ s hc0 hc hp₀ hP hs
  have hp0 : 0 < p₀ := by linarith
  have hterm : ∀ i ∈ Finset.range I, ∑ n ∈ s i, Real.log n / n ≤
      (4 * c + 1 / p₀) * Real.log (2 * X') := by
    intro i hi
    have hi' := Finset.mem_range.1 hi
    have h1 := band_sum (P i) c p₀ (s i) (hP i hi').1 hc0 hc hp₀ (hs i hi')
    have h2 : Real.log (2 * P i) ≤ Real.log (2 * X') :=
      Real.log_le_log (by linarith [(hP i hi').1]) (by linarith [(hP i hi').2])
    exact h1.trans (mul_le_mul_of_nonneg_left h2 (by positivity))
  have := Finset.sum_le_card_nsmul (Finset.range I) _ _ hterm
  rwa [Finset.card_range, nsmul_eq_mul] at this
end Formalism.LFunctionChainParameters.DeficitSplitLemmas
