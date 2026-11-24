-- Prove2me | solution 1 for Formalism.LogVandermondeBounds.product_first_zeroth_parts.bas_avoid
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:37:46.691042+00:00
-- url     : https://prove2.me/submissions/c62a40d9-fa0a-4b03-9b76-c6d033d5c6fc

import Definitions.Def_Formalism_LogVandermondeBounds_FinrankFiberSumZero
import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeProofs_MulSingleMulApplySelf

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
variable {ι H K : Type} [Fintype ι] [DecidableEq ι] [Group H] [Fintype H] [DecidableEq H] [Field K]
namespace Formalism.LogVandermondeBounds.product_first_zeroth_parts
theorem _root_.solution (a b : ι → {c : H // c ≠ 1}) :
    (bas a (fun w => (b w : H)) : K) = if a = b then 1 else 0 := by
  unfold bas
  by_cases hab : a = b
  · subst hab
    rw [if_pos rfl]
    refine Finset.prod_eq_one fun w _ => ?_
    unfold eps
    simp
  · rw [if_neg hab]
    have hw : ∃ w, a w ≠ b w := by
      by_contra hcon
      simp only [not_exists, not_not] at hcon
      exact hab (funext hcon)
    obtain ⟨w, hw⟩ := hw
    refine Finset.prod_eq_zero (mem_univ w) ?_
    have h1 : (b w : H) ≠ a w := fun h => hw (Subtype.ext h.symm)
    unfold eps
    simp [h1, (b w).2]
end Formalism.LogVandermondeBounds.product_first_zeroth_parts
