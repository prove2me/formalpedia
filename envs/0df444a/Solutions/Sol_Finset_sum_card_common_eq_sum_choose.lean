-- Prove2me | solution 1 for Finset.sum_card_common_eq_sum_choose
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T20:58:39.93914+00:00
-- url     : https://prove2.me/submissions/a6e30638-96fe-437a-b9e6-333da8a6deac

module
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Tactic.Rify
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Definitions.Def_ProbabilisticMethod_DependentRandomChoice

set_option autoImplicit true
@[expose] public section
public section
open Finset
open Finset
variable {α β : Type*}
namespace Finset
theorem _root_.solution (r : α → β → Prop) [∀ x y, Decidable (r x y)]
    (L : Finset α) (R : Finset β) (h : ℕ) :
    ∑ U ∈ L.powersetCard h, #{y ∈ R | ∀ x ∈ U, r x y} =
      ∑ y ∈ R, (#{x ∈ L | r x y}).choose h := by
  calc ∑ U ∈ L.powersetCard h, #{y ∈ R | ∀ x ∈ U, r x y}
      = ∑ U ∈ L.powersetCard h, ∑ y ∈ R, if ∀ x ∈ U, r x y then 1 else 0 :=
        sum_congr rfl fun U _ => card_filter _ _
    _ = ∑ y ∈ R, ∑ U ∈ L.powersetCard h, if ∀ x ∈ U, r x y then 1 else 0 := sum_comm
    _ = ∑ y ∈ R, #{U ∈ L.powersetCard h | ∀ x ∈ U, r x y} :=
        sum_congr rfl fun y _ => (card_filter _ _).symm
    _ = _ := sum_congr rfl fun y _ => ?_
  rw [← card_powersetCard]
  congr 1
  ext U
  simp only [mem_filter, mem_powersetCard, subset_iff]
  constructor
  · rintro ⟨⟨hUL, hU⟩, hr⟩
    exact ⟨fun x hx => ⟨hUL hx, hr x hx⟩, hU⟩
  · rintro ⟨hU, hcard⟩
    exact ⟨⟨fun x hx => (hU hx).1, hcard⟩, fun x hx => (hU hx).2⟩
end Finset
