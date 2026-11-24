-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.DeficitSplitLemmas.or_bucket_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:32:32.27908+00:00
-- url     : https://prove2.me/submissions/07388d80-eb31-4d1b-b41f-4b27595a5735

import Definitions.Def_Formalism_SizeWindowBrackets_SecondKindBucket
import Definitions.Def_Formalism_LogFactorialBounds_LogFactorialProofs_PrimeSum
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_RankGapDecayHypothesis
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_PmModulusFacts
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_FourNotDvdOddSqAddOne
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_AdmissibleSchurLemma
import Theorems.Thm_Formalism_LFunctionChainParameters_DeficitSplitLemmas_prime_log_sum_bound
import Theorems.Thm_Formalism_LFunctionChainParameters_DeficitSplitLemmas_tail_square_bound

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
theorem _root_.solution : OrBucket := by
  intro C lx La a k K₀ X' L₁ p₀ s hC hlx hLa ha hk hK₀ hX' hp₀ hs hL
  simp only [orF]
  have hterm : ∀ p ∈ s, 2 * Real.log p * (C * lx * (La * a / (p * k) +
        (if p < p₀ then a * (p : ℝ) ^ (-(L₁ p)) else a / (p : ℝ) ^ 2))) ≤
      2 * C * lx * a * (La / k) * (Real.log p / p) +
      (if p < p₀ then 2 * C * lx * a * (1 / K₀) * (Real.log p / p) else 0) +
      (if p₀ ≤ p then 2 * C * lx * a * (Real.log p / (p : ℝ) ^ 2) else 0) := by
    intro p hp
    have hpp := (hs p hp).1
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hpp.pos
    have hl : 0 ≤ Real.log p := Real.log_natCast_nonneg p
    by_cases hlt : p < p₀
    · rw [if_pos hlt, if_pos hlt, if_neg (by omega)]
      have hK := hL p hp hlt
      rw [Real.rpow_sub_one hp0.ne'] at hK
      have hpL : 0 < (p : ℝ) ^ (L₁ p) := Real.rpow_pos_of_pos hp0 _
      have hK' : K₀ * p ≤ (p : ℝ) ^ (L₁ p) := (le_div_iff₀ hp0).1 hK
      have hinv : (p : ℝ) ^ (-(L₁ p)) ≤ 1 / K₀ * (1 / p) := by
        rw [Real.rpow_neg hp0.le, ← one_div, one_div_mul_one_div]
        exact one_div_le_one_div_of_le (by positivity) hK'
      have h1 : a * (p : ℝ) ^ (-(L₁ p)) ≤ a * (1 / K₀ * (1 / p)) := mul_le_mul_of_nonneg_left hinv ha
      have h2 : 2 * Real.log p * (C * lx * (La * a / (p * k) + a * (p : ℝ) ^ (-(L₁ p)))) ≤
          2 * Real.log p * (C * lx * (La * a / (p * k) + a * (1 / K₀ * (1 / p)))) := by
        apply mul_le_mul_of_nonneg_left _ (by linarith)
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        linarith
      refine h2.trans (le_of_eq ?_)
      field_simp
      ring
    · rw [if_neg hlt, if_neg hlt, if_pos (by omega)]
      apply le_of_eq
      field_simp
      ring
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.sum_filter, ← Finset.sum_filter,
    ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
  have h1 := prime_log_sum_bound X' s hX' (fun p hp => ⟨(hs p hp).1, (hs p hp).2.le⟩)
  have h2 := prime_log_sum_bound X' (s.filter (fun p => p < p₀)) hX' (by
    intro p hp
    rw [Finset.mem_filter] at hp
    exact ⟨(hs p hp.1).1, (hs p hp.1).2.le⟩)
  have h3 := tail_square_bound p₀ (s.filter (fun p => p₀ ≤ p)) hp₀ (by
    intro p hp
    exact (Finset.mem_filter.1 hp).2)
  have h4 := mul_le_mul_of_nonneg_left h1 (show 0 ≤ 2 * C * lx * a * (La / k) by positivity)
  have h5 := mul_le_mul_of_nonneg_left h2 (show 0 ≤ 2 * C * lx * a * (1 / K₀) by positivity)
  have h6 := mul_le_mul_of_nonneg_left h3 (show 0 ≤ 2 * C * lx * a by positivity)
  refine (add_le_add (add_le_add h4 h5) h6).trans (le_of_eq ?_)
  ring
end Formalism.LFunctionChainParameters.DeficitSplitLemmas
