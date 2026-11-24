-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.DeficitSplitLemmas.tail_square_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:05:26.103874+00:00
-- url     : https://prove2.me/submissions/0cde03e8-a9fb-4ee5-badb-a2b111fa32ed

import Definitions.Def_Formalism_SizeWindowBrackets_SecondKindBucket
import Definitions.Def_Formalism_LogFactorialBounds_LogFactorialProofs_PrimeSum
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_RankGapDecayHypothesis
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_PmModulusFacts
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_FourNotDvdOddSqAddOne
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_AdmissibleSchurLemma
import Theorems.Thm_Formalism_LFunctionChainParameters_DeficitSplitLemmas_gT_nonneg
import Theorems.Thm_Formalism_LFunctionChainParameters_DeficitSplitLemmas_tail_Ico

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
theorem _root_.solution : TailSq := by
  intro p₀ s hp hs
  have hsub : s ⊆ Finset.Ico p₀ (p₀ + (s.sup id + 1)) := by
    intro n hn
    rw [Finset.mem_Ico]
    have : n ≤ s.sup id := Finset.le_sup (f := id) hn
    exact ⟨hs n hn, by omega⟩
  have h1 : ∑ n ∈ s, Real.log n / (n : ℝ) ^ 2 ≤
      ∑ n ∈ Finset.Ico p₀ (p₀ + (s.sup id + 1)), Real.log n / (n : ℝ) ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun n _ _ => div_nonneg (Real.log_natCast_nonneg n) (by positivity))
  have h2 := tail_Ico p₀ hp (s.sup id + 1)
  have hp' : (3 : ℝ) ≤ p₀ := by exact_mod_cast hp
  have h3 : 0 ≤ gT ((p₀ : ℝ) + ((s.sup id + 1 : ℕ) : ℝ) - 1) := by
    apply gT_nonneg
    have : (0 : ℝ) ≤ ((s.sup id + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
    linarith
  have e : 2 * (Real.log ((p₀ : ℝ) - 1) + 1) / ((p₀ : ℝ) - 1) = 2 * gT ((p₀ : ℝ) - 1) := by
    unfold gT; ring
  rw [e]
  linarith
end Formalism.LFunctionChainParameters.DeficitSplitLemmas
