-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.DeficitSplitLemmas.dsum_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:27:25.840889+00:00
-- url     : https://prove2.me/submissions/5747fe62-f0cd-4006-a7f3-d0b391cf5232

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
theorem _root_.solution {κ τ : Type*} (J : Finset κ) (S : Finset τ) (g : κ → τ → ℝ) (c : ℝ)
    (h : ∀ j ∈ J, ∀ t ∈ S, g j t ≤ c) :
    ∑ j ∈ J, ∑ t ∈ S, g j t ≤ (J.card : ℝ) * S.card * c := by
  have h1 : ∀ j ∈ J, ∑ t ∈ S, g j t ≤ S.card * c := by
    intro j hj
    have := Finset.sum_le_card_nsmul S _ c (h j hj)
    rwa [nsmul_eq_mul] at this
  have h2 := Finset.sum_le_card_nsmul J _ _ h1
  rw [nsmul_eq_mul] at h2
  calc _ ≤ (J.card : ℝ) * (S.card * c) := h2
    _ = _ := by ring
end Formalism.LFunctionChainParameters.DeficitSplitLemmas
