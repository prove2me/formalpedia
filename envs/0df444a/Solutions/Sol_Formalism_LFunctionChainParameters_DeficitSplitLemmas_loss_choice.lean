-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.DeficitSplitLemmas.loss_choice
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:38:54.742278+00:00
-- url     : https://prove2.me/submissions/985f05a0-eae3-45c4-8a6e-253c77a09502

import Definitions.Def_Formalism_SizeWindowBrackets_SecondKindBucket
import Definitions.Def_Formalism_LogFactorialBounds_LogFactorialProofs_PrimeSum
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_RankGapDecayHypothesis
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_PmModulusFacts
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_FourNotDvdOddSqAddOne
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_AdmissibleSchurLemma
import Theorems.Thm_Formalism_LFunctionChainParameters_DeficitSplitLemmas_second_kind_bucket_bound
import Theorems.Thm_Formalism_LFunctionChainParameters_DeficitSplitLemmas_io_mean_bound
import Theorems.Thm_Formalism_LFunctionChainParameters_DeficitSplitLemmas_choose_window_second

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
theorem _root_.solution : LossChoice := by
  intro Ω _ π Loss s Sig io D Y θ s₀ mTa hπ h1 hθ hs₀ hm hY hs hSig hmean hLoss hio
  have hA := second_kind_bucket_bound Ω π s Sig Y θ s₀ mTa hπ hθ hs₀ hm hY hSig hs hmean
  have hB := io_mean_bound Ω π s Sig (fun p o => 2 * Sig p o * (2 * mTa / p)) Y s₀ mTa hπ hs₀ hm hY
    hs hmean (fun p _ o => le_rfl)
  obtain ⟨o, ho, hFG, -, -⟩ := choose_window_second Ω π
    (fun o => ∑ p ∈ s, (if θ < Sig p o then 4 * mTa * Real.log p / p else 0))
    (fun o => ∑ p ∈ s, Real.log p * (2 * Sig p o * (2 * mTa / p)))
    _ _ hπ h1 (by
      intro o
      apply Finset.sum_nonneg
      intro p _
      split_ifs
      · exact div_nonneg (mul_nonneg (by linarith) (Real.log_natCast_nonneg p)) (Nat.cast_nonneg p)
      · exact le_rfl) (by
      intro o
      apply Finset.sum_nonneg
      intro p hp
      have h2 := hSig p hp o
      have h3 := Real.log_natCast_nonneg p
      have h4 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
      positivity) hA hB
  have hF0 : 0 ≤ ∑ p ∈ s, (if θ < Sig p o then 4 * mTa * Real.log p / p else 0) := by
    apply Finset.sum_nonneg
    intro p _
    split_ifs
    · exact div_nonneg (mul_nonneg (by linarith) (Real.log_natCast_nonneg p)) (Nat.cast_nonneg p)
    · exact le_rfl
  have hG0 : 0 ≤ ∑ p ∈ s, Real.log p * (2 * Sig p o * (2 * mTa / p)) := by
    apply Finset.sum_nonneg
    intro p hp
    have h2 := hSig p hp o
    have h3 := Real.log_natCast_nonneg p
    have h4 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
    positivity
  have hio' : ∑ p ∈ s, Real.log p * io p o ≤ ∑ p ∈ s, Real.log p * (2 * Sig p o * (2 * mTa / p)) :=
    Finset.sum_le_sum (fun p hp =>
      mul_le_mul_of_nonneg_left (hio p hp o) (Real.log_natCast_nonneg p))
  have e : (s₀ / θ + s₀) * (4 * mTa * (Real.log Y + Real.log 4)) =
      s₀ / θ * (4 * mTa * (Real.log Y + Real.log 4)) +
        4 * mTa * s₀ * (Real.log Y + Real.log 4) := by ring
  refine ⟨o, ho, ?_, ?_⟩
  · rw [e]; linarith [hLoss o]
  · rw [e]; linarith
end Formalism.LFunctionChainParameters.DeficitSplitLemmas
