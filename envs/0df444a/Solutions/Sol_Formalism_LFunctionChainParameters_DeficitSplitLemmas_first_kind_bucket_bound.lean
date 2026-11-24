-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.DeficitSplitLemmas.first_kind_bucket_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:28:50.51102+00:00
-- url     : https://prove2.me/submissions/783f11f3-d654-4cd1-9e31-560ff7378dbc

import Definitions.Def_Formalism_SizeWindowBrackets_SecondKindBucket
import Definitions.Def_Formalism_LogFactorialBounds_LogFactorialProofs_PrimeSum
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_RankGapDecayHypothesis
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_PmModulusFacts
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_FourNotDvdOddSqAddOne
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_AdmissibleSchurLemma
import Theorems.Thm_Formalism_LFunctionChainParameters_DeficitSplitLemmas_band_total
import Theorems.Thm_Formalism_RankGapBounds_LocalQuadraticParts_ordersSumY_of
import Theorems.Thm_Formalism_RankGapBounds_LocalQuadraticParts_powTwoPowEqOneIff_holds


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
theorem _root_.solution : FirstKindBucket := by
  obtain ⟨C, hC⟩ := Formalism.RankGapBounds.LocalQuadraticParts.ordersSumY_of Formalism.RankGapBounds.LocalQuadraticParts.powTwoPowEqOneIff_holds
  refine ⟨C, ?_⟩
  intro e J I Y X' c p₀ P s he hJ hY hc0 hc hp₀ hP hs
  have hf0 : ∀ p : ℕ, 0 ≤ Real.log p / (p : ℝ) :=
    fun p => div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg p)
  have hterm : ∀ p ∈ s, Real.log p / (p : ℝ) ≤
      (if ((p : ℝ) ≤ Y ∧ ∃ hl : Nat.Coprime p (4 * 2 ^ e),
          orderOf (Formalism.RankGapBounds.LocalQuadraticParts.hOf e p hl) ≤ J) then Real.log p / (p : ℝ) else 0) +
      ∑ i ∈ Finset.range I, (if (p₀ ≤ p ∧ P i * (1 - c) ≤ p ∧ (p : ℝ) ≤ P i * (1 + c)) then
          Real.log p / (p : ℝ) else 0) := by
    intro p hp
    have hsum0 : 0 ≤ ∑ i ∈ Finset.range I,
        (if (p₀ ≤ p ∧ P i * (1 - c) ≤ p ∧ (p : ℝ) ≤ P i * (1 + c)) then
          Real.log p / (p : ℝ) else 0) := by
      apply Finset.sum_nonneg
      intro i _
      split_ifs
      · exact hf0 p
      · exact le_rfl
    rcases (hs p hp).2.2 with h | ⟨i, hi, hb⟩
    · rw [if_pos h]; linarith
    · have h1 := Finset.single_le_sum (f := fun i =>
          (if (p₀ ≤ p ∧ P i * (1 - c) ≤ p ∧ (p : ℝ) ≤ P i * (1 + c)) then
            Real.log p / (p : ℝ) else 0)) (s := Finset.range I) (by
          intro i _
          split_ifs
          · exact hf0 p
          · exact le_rfl) (Finset.mem_range.2 hi)
      rw [if_pos hb] at h1
      have : 0 ≤ (if ((p : ℝ) ≤ Y ∧ ∃ hl : Nat.Coprime p (4 * 2 ^ e),
          orderOf (Formalism.RankGapBounds.LocalQuadraticParts.hOf e p hl) ≤ J) then Real.log p / (p : ℝ) else 0) := by
        split_ifs
        · exact hf0 p
        · exact le_rfl
      linarith
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_add_distrib, Finset.sum_comm, ← Finset.sum_filter]
  simp only [← Finset.sum_filter]
  apply add_le_add
  · apply hC e J Y _ he hJ hY
    intro l hl
    obtain ⟨hl1, hl2⟩ := Finset.mem_filter.1 hl
    exact ⟨(hs l hl1).1, (hs l hl1).2.1, hl2.1, hl2.2⟩
  · apply band_total I P X' c p₀ _ hc0 hc hp₀ hP
    intro i _ n hn
    exact (Finset.mem_filter.1 hn).2
end Formalism.LFunctionChainParameters.DeficitSplitLemmas
