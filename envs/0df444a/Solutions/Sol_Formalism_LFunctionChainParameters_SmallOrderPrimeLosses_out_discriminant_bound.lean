-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.SmallOrderPrimeLosses.out_discriminant_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:30:47.944479+00:00
-- url     : https://prove2.me/submissions/02684da3-a90f-4f44-8df8-e34c8b841739

import Definitions.Def_Formalism_SizeWindowBrackets_PrimeClassLossHypothesesSatisfiable
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_OneLeThresholdMulPowers
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_DiscriminantSettingSatisfied
import Theorems.Thm_Formalism_LFunctionChainParameters_SmallOrderPrimeLosses_logdiv_nonneg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.SmallOrderPrimeLosses
open Finset Classical
open Formalism.LFunctionChainParameters.DeficitSplitLemmas Formalism.LFunctionChainParameters.LErr Formalism.LFunctionChainParameters.PrimeWindowSizeBounds
namespace Formalism.LFunctionChainParameters.SmallOrderPrimeLosses
theorem _root_.solution : OutD := by
  intro τ Ps PR cl TT TTp BAD m a R hm ha hT2 hBad
  have hco : ∀ p : ℕ, 0 ≤ 4 * m * a * (Real.log p / p) := fun p => by
    have := logdiv_nonneg p
    positivity
  have h1 : ∑ p ∈ Ps.filter (fun p => cl p = PClass.served),
      4 * m * a * (Real.log p / p) * ((TT \ TTp p).card : ℝ) ≤
      ∑ p ∈ Ps.filter (fun p => cl p = PClass.served),
        (if p ∈ PR then 4 * m * a * (Real.log p / p) * ((TT.filter fun t => BAD p t).card : ℝ)
          else 0) := by
    refine Finset.sum_le_sum (fun p hp => ?_)
    rw [Finset.mem_filter] at hp
    have hb := hBad p hp.1 hp.2
    by_cases hps : p ∈ PR
    · rw [if_pos hps]
      refine mul_le_mul_of_nonneg_left ?_ (hco p)
      have hsub : TT \ TTp p ⊆ TT.filter fun t => BAD p t := by
        intro t ht
        rw [Finset.mem_filter]
        exact ⟨(Finset.mem_sdiff.1 ht).1, (hb t ht).2⟩
      exact_mod_cast Finset.card_le_card hsub
    · rw [if_neg hps]
      have hemp : TT \ TTp p = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro t ht
        exact hps (hb t ht).1
      rw [hemp]; simp
  have h2 : ∑ p ∈ Ps.filter (fun p => cl p = PClass.served),
        (if p ∈ PR then 4 * m * a * (Real.log p / p) * ((TT.filter fun t => BAD p t).card : ℝ)
          else 0) ≤
      ∑ p ∈ PR, 4 * m * a * (Real.log p / p) * ((TT.filter fun t => BAD p t).card : ℝ) := by
    rw [← Finset.sum_filter]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun p _ _ => mul_nonneg (hco p) (Nat.cast_nonneg _))
    intro p hp
    exact (Finset.mem_filter.1 hp).2
  have h3 : ∑ p ∈ PR, 4 * m * a * (Real.log p / p) * ((TT.filter fun t => BAD p t).card : ℝ) =
      4 * a * m * badPrimeLogWeightedCount PR TT BAD := by
    unfold badPrimeLogWeightedCount
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun p _ => by ring)
  have h4 : 4 * a * m * badPrimeLogWeightedCount PR TT BAD ≤ 4 * a * m * R :=
    mul_le_mul_of_nonneg_left hT2 (by positivity)
  linarith
end Formalism.LFunctionChainParameters.SmallOrderPrimeLosses
