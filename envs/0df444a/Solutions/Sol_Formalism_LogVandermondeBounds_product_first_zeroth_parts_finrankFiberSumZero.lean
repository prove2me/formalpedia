-- Prove2me | solution 1 for Formalism.LogVandermondeBounds.product_first_zeroth_parts.finrankFiberSumZero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:11:29.367748+00:00
-- url     : https://prove2.me/submissions/d952b1f2-8c62-445f-ba7c-b8251b5f0458

import Definitions.Def_Formalism_LogVandermondeBounds_FinrankFiberSumZero
import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeProofs_MulSingleMulApplySelf
import Theorems.Thm_Formalism_LogVandermondeBounds_product_first_zeroth_parts_finrank_core
import Theorems.Thm_Formalism_LogVandermondeBounds_product_first_zeroth_parts_exists_equiv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.LogVandermondeBounds Formalism.LogVandermondeBounds.product_first_zeroth_parts
open Finset
namespace Formalism.LogVandermondeBounds.product_first_zeroth_parts
theorem _root_.solution : FinrankFiberSumZero := by
  intro ι H X K _ _ _ _ _ _ _ hfree
  classical
  obtain ⟨Q, _, e, he⟩ := exists_equiv ι H X hfree
  rw [finrank_core (K := K) Q e he, ← Fintype.card_congr e, Fintype.card_prod, Fintype.card_fun]
  ring
end Formalism.LogVandermondeBounds.product_first_zeroth_parts
