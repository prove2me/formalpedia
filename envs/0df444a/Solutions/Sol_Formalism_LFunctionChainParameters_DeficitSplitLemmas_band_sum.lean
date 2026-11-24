-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.DeficitSplitLemmas.band_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:41:37.907901+00:00
-- url     : https://prove2.me/submissions/84689d53-52ac-4957-9a98-019fdab78f75

import Definitions.Def_Formalism_SizeWindowBrackets_SecondKindBucket
import Definitions.Def_Formalism_LogFactorialBounds_LogFactorialProofs_PrimeSum
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_RankGapDecayHypothesis
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_PmModulusFacts
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_FourNotDvdOddSqAddOne
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_AdmissibleSchurLemma
import Theorems.Thm_Formalism_LFunctionChainParameters_DeficitSplitLemmas_band_count

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
theorem _root_.solution : BandSum := by
  intro P c p₀ s hP hc0 hc hp₀ hs
  have hP0 : 0 < P := by linarith
  have hp0 : 0 < p₀ := by linarith
  have hcard := band_count P c s hP0.le hc0 (fun n hn => (hs n hn).2)
  set μ := min (2 / P) (1 / p₀) with hμ
  have hμ0 : 0 ≤ μ := le_min (by positivity) (by positivity)
  have hl2P : 0 ≤ Real.log (2 * P) := Real.log_nonneg (by linarith)
  have hterm : ∀ n ∈ s, Real.log n / n ≤ Real.log (2 * P) * μ := by
    intro n hn
    obtain ⟨h1, h2, h3⟩ := hs n hn
    have hn0 : (0 : ℝ) < n := by linarith
    have hlog : Real.log n ≤ Real.log (2 * P) := Real.log_le_log hn0 (by nlinarith)
    have hinv : 1 / (n : ℝ) ≤ μ := by
      apply le_min
      · rw [div_le_div_iff₀ hn0 hP0]; nlinarith
      · exact one_div_le_one_div_of_le hp0 h1
    calc Real.log n / n = Real.log n * (1 / (n : ℝ)) := by ring
      _ ≤ Real.log (2 * P) * μ :=
        mul_le_mul hlog hinv (by positivity) hl2P
  have hsum : ∑ n ∈ s, Real.log n / n ≤ s.card * (Real.log (2 * P) * μ) := by
    have := Finset.sum_le_card_nsmul s _ _ hterm
    rwa [nsmul_eq_mul] at this
  have hcμ : (s.card : ℝ) * μ ≤ 4 * c + 1 / p₀ := by
    have h1 : (s.card : ℝ) * μ ≤ (2 * c * P + 1) * μ := mul_le_mul_of_nonneg_right hcard hμ0
    have h2 : 2 * c * P * μ ≤ 2 * c * P * (2 / P) :=
      mul_le_mul_of_nonneg_left (min_le_left _ _) (by positivity)
    have h3 : μ ≤ 1 / p₀ := min_le_right _ _
    have e : 2 * c * P * (2 / P) = 4 * c := by field_simp; ring
    nlinarith
  calc ∑ n ∈ s, Real.log n / n ≤ s.card * (Real.log (2 * P) * μ) := hsum
    _ = (s.card * μ) * Real.log (2 * P) := by ring
    _ ≤ (4 * c + 1 / p₀) * Real.log (2 * P) := mul_le_mul_of_nonneg_right hcμ hl2P
end Formalism.LFunctionChainParameters.DeficitSplitLemmas
