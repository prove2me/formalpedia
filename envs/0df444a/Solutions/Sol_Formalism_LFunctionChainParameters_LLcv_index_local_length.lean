-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LLcv.index_local_length
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:35:55.115784+00:00
-- url     : https://prove2.me/submissions/9024354e-1727-4a76-adf3-1e3fbb3f5c0b

import Definitions.Def_Formalism_SizeWindowBrackets_LcvBaseChange
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_ExistsNsmulMem
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_TruncatedLatticeHolds
import Theorems.Thm_Formalism_LFunctionChainParameters_LLcv_indexLocLen_finsupp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField
noncomputable section
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.LLcv
open Formalism.HN Formalism.HermitianLatticesTheory Formalism.LFunctionChainParameters.slopeLatticeData
namespace Formalism.LFunctionChainParameters.LLcv
theorem _root_.solution : IndexLocLen := by
  intro K V _ _ _ _ A B hBA h
  obtain ⟨k, hk, hc⟩ := indexLocLen_finsupp A B hBA h
  have hl : ∀ w : {p : Ideal (𝓞 K) // p.IsMaximal},
      (haveI := w.2.isPrime; Formalism.HermitianLatticesTheory.locLen w.1 A B) = k w := by
    intro w
    have := hk w
    unfold pLen at this
    unfold Formalism.HermitianLatticesTheory.locLen
    rw [this, ENat.toNat_natCast]
  refine ⟨fun w => ?_, ?_, ?_⟩
  · have := hk w
    unfold pLen at this
    rw [this]; exact ENat.natCast_ne_top _
  · refine k.support.finite_toSet.subset fun w hw => ?_
    rw [Function.mem_support, hl] at hw
    rw [Finset.mem_coe, Finsupp.mem_support_iff]
    exact hw
  · rw [hc, finsum_eq_sum_of_support_subset (s := k.support)]
    · refine Finset.sum_congr rfl fun w _ => ?_
      rw [hl]
    · intro w hw
      rw [Function.mem_support, hl] at hw
      rw [Finset.mem_coe, Finsupp.mem_support_iff]
      intro h0
      rw [h0] at hw
      simp at hw
end Formalism.LFunctionChainParameters.LLcv
