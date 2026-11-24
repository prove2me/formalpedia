-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.DeficitSplitLemmas.pr_bucket_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:27:29.539878+00:00
-- url     : https://prove2.me/submissions/fe799e75-c310-458c-9e6c-bfee038d4353

import Definitions.Def_Formalism_SizeWindowBrackets_SecondKindBucket
import Definitions.Def_Formalism_LogFactorialBounds_LogFactorialProofs_PrimeSum
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_RankGapDecayHypothesis
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_PmModulusFacts
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_FourNotDvdOddSqAddOne
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_AdmissibleSchurLemma
import Theorems.Thm_Formalism_LFunctionChainParameters_DeficitSplitLemmas_theta_finite

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
theorem _root_.solution : PrBucket := by
  intro p₀ X' Q₁ Q₂ s hX' hQ₁ hQ₂ hs
  simp only [prF]
  have hterm : ∀ p ∈ s, 2 * Real.log p * (if p < p₀ then Q₁ else Q₂) ≤
      (if p < p₀ then 2 * Q₁ * Real.log p else 0) + 2 * Q₂ * Real.log p := by
    intro p _
    have hl : 0 ≤ Real.log p := Real.log_natCast_nonneg p
    split_ifs
    · nlinarith [mul_nonneg hQ₂ hl]
    · linarith
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_add_distrib, ← Finset.sum_filter, ← Finset.mul_sum, ← Finset.mul_sum]
  have h1 := theta_finite p₀ (s.filter (fun p : ℕ => p < p₀)) (Nat.cast_nonneg _) (by
    intro p hp
    rw [Finset.mem_filter] at hp
    exact ⟨(hs p hp.1).1, by exact_mod_cast hp.2.le⟩)
  have h2 := theta_finite X' s hX' (fun p hp => ⟨(hs p hp).1, (hs p hp).2.le⟩)
  have h3 := mul_le_mul_of_nonneg_left h1 (show 0 ≤ 2 * Q₁ by linarith)
  have h4 := mul_le_mul_of_nonneg_left h2 (show 0 ≤ 2 * Q₂ by linarith)
  linarith
end Formalism.LFunctionChainParameters.DeficitSplitLemmas
