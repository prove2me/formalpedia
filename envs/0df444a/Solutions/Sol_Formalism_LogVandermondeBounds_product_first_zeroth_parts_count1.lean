-- Prove2me | solution 1 for Formalism.LogVandermondeBounds.product_first_zeroth_parts.count1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:59:11.086404+00:00
-- url     : https://prove2.me/submissions/b8a783cf-314f-4528-aeb9-02f76d391f53

import Definitions.Def_Formalism_LogVandermondeBounds_FinrankFiberSumZero
import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeProofs_RamifiedLatticeOperatorIdentity
import Theorems.Thm_Formalism_LogVandermondeBounds_product_first_zeroth_parts_pair_single_left
import Theorems.Thm_Formalism_LogVandermondeBounds_product_first_zeroth_parts_exists_coord_ne_zero
import Theorems.Thm_Formalism_LogVandermondeBounds_product_first_zeroth_parts_card_fiber_mul
import Theorems.Thm_Formalism_LogVandermondeBounds_product_first_zeroth_parts_pairL_apply

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
variable {k : Type*} [Field k] [Fintype k] [DecidableEq k] {r : ℕ} {R : Type*} [CommRing R]
namespace Formalism.LogVandermondeBounds.product_first_zeroth_parts
theorem _root_.solution {x : Fin r → k} (hx : x ≠ 0) (a : k) :
    (univ.filter (fun f : Fin r → k => pair f x = a)).card = Fintype.card k ^ (r - 1) := by
  obtain ⟨i, hi⟩ := exists_coord_ne_zero hx
  have hL : Function.Surjective (pairL x) := fun a =>
    ⟨Pi.single i (a / x i), by rw [pairL_apply, pair_single_left, div_mul_cancel₀ _ hi]⟩
  have h := card_fiber_mul k (pairL x) hL a
  have hq : 0 < Fintype.card k := Fintype.card_pos
  have hr : r - 1 + 1 = r := by have := i.pos; omega
  apply Nat.eq_of_mul_eq_mul_right hq
  rw [← pow_succ, hr]
  exact h
end Formalism.LogVandermondeBounds.product_first_zeroth_parts
