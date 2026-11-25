-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.RowTiePSplit.aff_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:33:27.800798+00:00
-- url     : https://prove2.me/submissions/d93f7bfc-74f2-4733-9a91-361f09bbcba3

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePSplitDef
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePSplitLA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.L2.FormalSeriesBounds.RowTiePSplit
open Polynomial Matrix
variable {K : Type} [Field K] [CharZero K]
namespace Formalism.L2.FormalSeriesBounds.RowTiePSplit
theorem _root_.solution (α β : K) (h : α ≠ 0 ∨ β ≠ 0) : {t : ℕ | α + (t : K) * β = 0}.Subsingleton := by
  intro t1 h1 t2 h2
  simp only [Set.mem_setOf_eq] at h1 h2
  by_cases hb : β = 0
  · rw [hb, mul_zero, add_zero] at h1
    exact absurd h1 (h.resolve_right (not_not.mpr hb))
  · have h3 : ((t1 : K) - t2) * β = 0 := by linear_combination h1 - h2
    have h4 : (t1 : K) = t2 := sub_eq_zero.mp ((mul_eq_zero.mp h3).resolve_right hb)
    exact_mod_cast h4
end Formalism.L2.FormalSeriesBounds.RowTiePSplit
