-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.TW.index_additive
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:44:13.077735+00:00
-- url     : https://prove2.me/submissions/1c163ca4-32c7-4553-aa8a-5ab2a55f50d8

import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_CentralIdempotentIntegral
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_TWIndexAdditive
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_TW_Idx_isLat_inf
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_TW_Idx_relLen_ne_top
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_TW_Idx_sIdx_eq_sub

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.TW
namespace Formalism.IrreducibleCountingLemmas.TW
theorem _root_.solution : IndexAdditive := by
  intro O K V _ _ _ _ _ _ _ _ _ _ _ M N P hM hN hP
  refine ⟨Idx.relLen_ne_top hM hN, ?_⟩
  have hQ := Idx.isLat_inf (Idx.isLat_inf hM hN) hP
  have q1 : M ⊓ N ⊓ P ≤ M := inf_le_left.trans inf_le_left
  have q2 : M ⊓ N ⊓ P ≤ N := inf_le_left.trans inf_le_right
  have q3 : M ⊓ N ⊓ P ≤ P := inf_le_right
  rw [Idx.sIdx_eq_sub hM hN hQ q1 q2, Idx.sIdx_eq_sub hN hP hQ q2 q3, Idx.sIdx_eq_sub hM hP hQ q1 q3]
  ring
end Formalism.IrreducibleCountingLemmas.TW
