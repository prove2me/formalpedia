-- Prove2me | solution 1 for Formalism.LogVandermondeBounds.StandardLattice.cardGeneralLinear
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:52:58.819328+00:00
-- url     : https://prove2.me/submissions/fe6d6d7a-1e60-4f33-9c6b-18c3e0cf251b

import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeVariationUnbounded
import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeProofs_CardStabilizerVector
import Theorems.Thm_Formalism_LogVandermondeBounds_StandardLattice_half_add_half
import Theorems.Thm_Formalism_LogVandermondeBounds_StandardLattice_factor_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.LogVandermondeBounds Formalism.LogVandermondeBounds.StandardLattice
open Finset
namespace Formalism.LogVandermondeBounds.StandardLattice
theorem _root_.solution : CardGeneralLinear := by
  intro F _ _ _ n
  have hpos : 0 < Fintype.card F := Fintype.card_pos
  have hq0 : (Fintype.card F : ℝ) ≠ 0 := by exact_mod_cast hpos.ne'
  have hnat : Fintype.card (GL (Fin n) F) =
      ∏ i ∈ range n, (Fintype.card F ^ n - Fintype.card F ^ i) := by
    rw [Finset.prod_range, Fintype.card_eq_nat_card (α := GL (Fin n) F)]
    exact Matrix.card_GL_field n
  have hreal : (Fintype.card (GL (Fin n) F) : ℝ) =
      ∏ i ∈ range n, ((Fintype.card F : ℝ) ^ n - (Fintype.card F : ℝ) ^ i) := by
    rw [hnat, Nat.cast_prod]
    refine Finset.prod_congr rfl (fun i hi => ?_)
    rw [Nat.cast_sub (Nat.pow_le_pow_right hpos (mem_range.mp hi).le), Nat.cast_pow, Nat.cast_pow]
  rw [hreal, ← pow_add, half_add_half]
  have hpow : (Fintype.card F : ℝ) ^ (n * n) = ∏ _i ∈ range n, (Fintype.card F : ℝ) ^ n := by
    rw [prod_const, card_range, ← pow_mul]
  have hrefl : ∏ j ∈ range n, ((Fintype.card F : ℝ) ^ n - (Fintype.card F : ℝ) ^ (n - 1 - j)) =
      ∏ j ∈ range n, ((Fintype.card F : ℝ) ^ n - (Fintype.card F : ℝ) ^ j) :=
    prod_range_reflect (fun i => (Fintype.card F : ℝ) ^ n - (Fintype.card F : ℝ) ^ i) n
  rw [hpow, ← prod_mul_distrib, ← hrefl]
  refine prod_congr rfl (fun i hi => ?_)
  have hi' := mem_range.mp hi
  rw [factor_eq _ hq0 n (n - 1 - i) (by omega), show n - (n - 1 - i) = i + 1 by omega]
end Formalism.LogVandermondeBounds.StandardLattice
