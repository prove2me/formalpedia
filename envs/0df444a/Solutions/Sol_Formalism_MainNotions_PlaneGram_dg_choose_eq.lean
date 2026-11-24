-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.dg_choose_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:33:12.758574+00:00
-- url     : https://prove2.me/submissions/8148715d-b148-4efd-88fe-5290908c2396

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_AddMemSupportOfMemSupportCoefOut
import Theorems.Thm_Formalism_MainNotions_PlaneGram_dg_eq_sum
import Theorems.Thm_Formalism_MainNotions_PlaneGram_prod_choose_single

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.MainNotions Formalism.MainNotions.PlaneGram
variable {K : Type} [Field K] [CharZero K] {L : Type} [Fintype L] [DecidableEq L] {r : ℕ} [NeZero r]
  {sg : L → Bool} {S : Finset L}
omit [CharZero K] [Fintype L] [NeZero r]
namespace Formalism.MainNotions.PlaneGram
theorem _root_.solution {σ : Type} (x : σ) (k : ℕ) (F : MvPolynomial σ K) :
    dg (fun α => ((α x).choose k : K)) F =
      monomial (Finsupp.single x k) 1 * ddiv (Finsupp.single x k) F := by
  rw [dg_eq_sum]
  unfold ddiv
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  split_ifs with h
  · have hk : k ≤ α x := Finsupp.single_le_iff.mp h
    rw [monomial_mul, add_tsub_cancel_of_le h, one_mul, prod_choose_single α x k hk, mul_comm]
  · have hk : α x < k := by
      by_contra hh
      exact h (Finsupp.single_le_iff.mpr (not_lt.mp hh))
    rw [Nat.choose_eq_zero_of_lt hk, Nat.cast_zero, zero_mul, monomial_zero, mul_zero]
end Formalism.MainNotions.PlaneGram
