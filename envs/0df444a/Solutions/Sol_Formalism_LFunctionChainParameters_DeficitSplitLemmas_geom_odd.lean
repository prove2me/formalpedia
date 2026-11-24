-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.DeficitSplitLemmas.geom_odd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:27:23.758074+00:00
-- url     : https://prove2.me/submissions/d405fc8d-77f7-4db4-b8c5-5686f8beb818

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
theorem _root_.solution (I : Finset ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq : q ≤ 1 / 2) (hI : ∀ i ∈ I, Odd i) :
    ∑ i ∈ I, q ^ i ≤ 4 / 3 * q := by
  set K := I.sup id + 1
  have hsub : I ⊆ (Finset.range K).image (fun k => 2 * k + 1) := by
    intro i hi
    obtain ⟨k, hk⟩ := hI i hi
    rw [Finset.mem_image]
    have : i ≤ I.sup id := Finset.le_sup (f := id) hi
    exact ⟨k, Finset.mem_range.2 (by omega), hk.symm⟩
  have h1 : ∑ i ∈ I, q ^ i ≤ ∑ i ∈ (Finset.range K).image (fun k => 2 * k + 1), q ^ i :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => pow_nonneg hq0 i)
  rw [Finset.sum_image (by intro a _ b _ h; simpa using h)] at h1
  have h2 : ∑ k ∈ Finset.range K, q ^ (2 * k + 1) = q * ∑ k ∈ Finset.range K, (q ^ 2) ^ k := by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro k _; rw [pow_succ, pow_mul]; ring
  have hq2 : q ^ 2 ≤ 1 / 4 := by nlinarith
  have h3 : ∑ k ∈ Finset.range K, (q ^ 2) ^ k ≤ 4 / 3 := by
    have := geom_sum_Ico_le_of_lt_one (x := q ^ 2) (m := 0) (n := K) (sq_nonneg q) (by linarith)
    rw [Finset.range_eq_Ico]
    refine this.trans ?_
    rw [pow_zero, div_le_iff₀ (by linarith)]
    linarith
  rw [h2] at h1
  nlinarith [mul_le_mul_of_nonneg_left h3 hq0]
end Formalism.LFunctionChainParameters.DeficitSplitLemmas
