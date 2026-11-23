-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.DeficitSplitLemmas.deficit_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:34:51.470641+00:00
-- url     : https://prove2.me/submissions/bc834c5b-f5c0-4ba8-83c6-7d0deb32b6cb

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
theorem _root_.solution {κ τ : Type*} (J : Finset κ) (TT : Finset τ) (TTp : ℕ → Finset τ)
    (vonMangoldtClassSum : κ → τ → ℕ → ℝ) (gain : κ → ℕ → ℝ) (tau lo fl : ℕ → ℝ) (p : ℕ)
    (h : SizeData₂ J TT TTp vonMangoldtClassSum gain tau lo fl p) :
    deficit J TT vonMangoldtClassSum gain tau p ≤ servedLoss J TT TTp vonMangoldtClassSum lo fl p := by
  obtain ⟨hsub, hled⟩ := h
  unfold deficit servedLoss
  have h1 : ∑ j ∈ J, ∑ t ∈ TT, vonMangoldtClassSum j t p =
      ∑ j ∈ J, ∑ t ∈ TT \ TTp p, vonMangoldtClassSum j t p + ∑ j ∈ J, ∑ t ∈ TTp p, vonMangoldtClassSum j t p := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun j _ => (Finset.sum_sdiff hsub).symm)
  have h2 : ∑ j ∈ J, ∑ t ∈ TTp p, (vonMangoldtClassSum j t p - lo p) =
      ∑ j ∈ J, ∑ t ∈ TTp p, vonMangoldtClassSum j t p - (J.card : ℝ) * (TTp p).card * lo p := by
    simp only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]; ring
  rw [h1]
  rw [h2] at hled
  linarith
end Formalism.LFunctionChainParameters.DeficitSplitLemmas
