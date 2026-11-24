-- Prove2me | solution 1 for Formalism.LogVandermondeBounds.product_first_zeroth_parts.count2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:59:08.084667+00:00
-- url     : https://prove2.me/submissions/9953f293-3132-4688-95bf-055db27b486a

import Definitions.Def_Formalism_LogVandermondeBounds_FinrankFiberSumZero
import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeProofs_RamifiedLatticeOperatorIdentity
import Theorems.Thm_Formalism_LogVandermondeBounds_product_first_zeroth_parts_pair_single_left
import Theorems.Thm_Formalism_LogVandermondeBounds_product_first_zeroth_parts_exists_coord_ne_zero
import Theorems.Thm_Formalism_LogVandermondeBounds_product_first_zeroth_parts_card_fiber_mul
import Theorems.Thm_Formalism_LogVandermondeBounds_product_first_zeroth_parts_pairTwoLinear_apply

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
theorem _root_.solution (hr : 2 ≤ r) {x y : Fin r → k} (hx : x ≠ 0) (hy : ∀ c : k, y ≠ c • x) (a b : k) :
    (univ.filter (fun f : Fin r → k => pair f x = a ∧ pair f y = b)).card =
      Fintype.card k ^ (r - 2) := by
  have hminor : ∃ i j, x i * y j - x j * y i ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨i, hi⟩ := exists_coord_ne_zero hx
    apply hy (y i / x i)
    funext j
    have := hcon i j
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [div_mul_eq_mul_div, eq_div_iff hi]
    linear_combination this
  obtain ⟨i, j, hD⟩ := hminor
  have hL : Function.Surjective (pairTwoLinear x y) := by
    rintro ⟨a, b⟩
    refine ⟨Pi.single i ((a * y j - b * x j) / (x i * y j - x j * y i)) +
      Pi.single j ((b * x i - a * y i) / (x i * y j - x j * y i)), ?_⟩
    rw [pairTwoLinear_apply, pair_add_left, pair_add_left, pair_single_left, pair_single_left,
      pair_single_left, pair_single_left]
    refine Prod.ext ?_ ?_
    · dsimp only
      rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, div_eq_iff hD]; ring
    · dsimp only
      rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, div_eq_iff hD]; ring
  have h := card_fiber_mul (k × k) (pairTwoLinear x y) hL (a, b)
  have hfil : univ.filter (fun f : Fin r → k => pair f x = a ∧ pair f y = b) =
      univ.filter (fun f => pairTwoLinear x y f = (a, b)) := by
    ext f; simp [pairTwoLinear_apply]
  rw [hfil]
  have hq : 0 < Fintype.card k * Fintype.card k := Nat.mul_pos Fintype.card_pos Fintype.card_pos
  apply Nat.eq_of_mul_eq_mul_right hq
  rw [Fintype.card_prod] at h
  rw [h, ← mul_assoc, ← pow_succ, ← pow_succ]
  congr 1; omega
end Formalism.LogVandermondeBounds.product_first_zeroth_parts
