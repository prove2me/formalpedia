-- Prove2me | solution 1 for Finset.exists_card_common_ge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:03:09.679791+00:00
-- url     : https://prove2.me/submissions/84770af5-3925-4242-8b35-5ec2d8b071e4

module
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Tactic.Rify
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Definitions.Def_ProbabilisticMethod_DependentRandomChoice
public import Theorems.Thm_Finset_sum_card_common_eq_sum_choose

set_option autoImplicit true
@[expose] public section
public section
open Finset
open Finset
variable {α β : Type*}
namespace Finset
theorem _root_.solution (r : α → β → Prop) [∀ x y, Decidable (r x y)] {L : Finset α}
    {R : Finset β} {h t : ℕ} (hh : h ≤ #L)
    (hmoment : t * (#L).choose h ≤ ∑ y ∈ R, (#{x ∈ L | r x y}).choose h) :
    ∃ U ⊆ L, #U = h ∧ t ≤ #{y ∈ R | ∀ x ∈ U, r x y} := by
  rw [← sum_card_common_eq_sum_choose] at hmoment
  by_contra! hlt
  have hne : (L.powersetCard h).Nonempty := powersetCard_nonempty.mpr hh
  have := sum_lt_sum_of_nonempty hne fun U hU =>
    hlt U (mem_powersetCard.mp hU).1 (mem_powersetCard.mp hU).2
  rw [sum_const, card_powersetCard, smul_eq_mul, mul_comm] at this
  omega
end Finset
