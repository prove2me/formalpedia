-- Prove2me | solution 1 for Formalism.LogVandermondeBounds.product_first_zeroth_parts.sum_bas
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:38:58.536994+00:00
-- url     : https://prove2.me/submissions/e4f8cffe-29e8-4cf1-adc4-d50104a6c0f6

import Definitions.Def_Formalism_LogVandermondeBounds_FinrankFiberSumZero
import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeProofs_MulSingleMulApplySelf
import Theorems.Thm_Formalism_LogVandermondeBounds_product_first_zeroth_parts_mulSingle_mul_apply_ne
import Theorems.Thm_Formalism_LogVandermondeBounds_product_first_zeroth_parts_mulSingle_mul_apply_self
import Theorems.Thm_Formalism_LogVandermondeBounds_product_first_zeroth_parts_sum_eps

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
theorem _root_.solution (a : ι → {c : H // c ≠ 1}) (v : ι) (h : ι → H) :
    ∑ c : H, (bas a ((Pi.mulSingle v c : ι → H) * h) : K) = 0 := by
  have hfac : ∀ c : H, (bas a ((Pi.mulSingle v c : ι → H) * h) : K)
      = (eps (a v : H) (c * h v) : K) * ∏ w ∈ univ.erase v, (eps (a w : H) (h w) : K) := by
    intro c
    unfold bas
    rw [← Finset.mul_prod_erase univ _ (mem_univ v)]
    simp only [mulSingle_mul_apply_self]
    congr 1
    refine Finset.prod_congr rfl fun w hw => ?_
    rw [mulSingle_mul_apply_ne v w c h (Finset.ne_of_mem_erase hw)]
  simp only [hfac, ← Finset.sum_mul, sum_eps (K := K) (a v : H) (h v) (a v).2, zero_mul]
end Formalism.LogVandermondeBounds.product_first_zeroth_parts
