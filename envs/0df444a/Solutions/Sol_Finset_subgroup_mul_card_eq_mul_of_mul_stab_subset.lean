-- Prove2me | solution 1 for Finset.subgroup_mul_card_eq_mul_of_mul_stab_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:59:36.091829+00:00
-- url     : https://prove2.me/submissions/56824ae6-2f39-4284-bbba-b2c8841ba0c0

module
public import Mathlib.Algebra.Pointwise.Stabilizer
public import Mathlib.GroupTheory.Coset.Card
public import Mathlib.GroupTheory.GroupAction.Blocks
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Definitions.Def_Erdos338_Kneser_MulStab
public import Theorems.Thm_Finset_card_mulStab_dvd_card_mulStab
public import Theorems.Thm_P2M_Finset_card_mulStab_mul_card_image_coe__56c0b835d7e6
public import Theorems.Thm_Finset_card_mul_card_eq_mulStab_card_mul_coe
public import Theorems.Thm_Finset_card_mulStab_mul_card_image_coe

set_option autoImplicit true
@[expose] public section
public section
open Function MulAction
open scoped Pointwise
open Finset
variable {ι α : Type*}
local notation s " +ₛ " N => Finset.image ((↑) : α → α ⧸ N) s
local notation s " +ˢ " N => Set.image ((↑) : α → α ⧸ N) s
variable [CommGroup α] [DecidableEq α] {s t : Finset α} {a : α}
namespace Finset
theorem _root_.solution (s : Subgroup α) [DecidablePred (· ∈ s)]
    (t : Finset α) (hst : (s : Set α) ⊆ t.mulStab) : Nat.card s * #(t +ₛ s) = #t := by
  suffices h : (t : Set α) * s = t by
    simpa [h, eq_comm] using s.card_mul_eq_card_subgroup_mul_card_quotient  t
  apply Set.Subset.antisymm (Set.Subset.trans (Set.mul_subset_mul_left hst) _)
  · intro x
    rw [Set.mem_mul]
    aesop
  · rw [← coe_mul, mul_mulStab]
end Finset
