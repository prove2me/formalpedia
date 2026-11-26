-- Prove2me | solution 1 for Finset.card_mul_card_eq_mulStab_card_mul_coe
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:58:03.204675+00:00
-- url     : https://prove2.me/submissions/cea1e06e-496a-4495-b5c0-cb6ccf6681ec

module
public import Mathlib.Algebra.Pointwise.Stabilizer
public import Mathlib.GroupTheory.Coset.Card
public import Mathlib.GroupTheory.GroupAction.Blocks
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Definitions.Def_Erdos338_Kneser_MulStab
public import Theorems.Thm_Finset_card_mulStab_dvd_card_mulStab
public import Theorems.Thm_P2M_Finset_card_mulStab_mul_card_image_coe__56c0b835d7e6

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
theorem _root_.solution (s t : Finset α) :
    #(s * t) = #(s * t).mulStab * #((s * t) +ₛ stabilizer α (↑(s * t) : Set α)) := by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · simp
  obtain rfl | ht := t.eq_empty_or_nonempty
  · simp
  have := QuotientGroup.preimageMkEquivSubgroupProdSet _ <|
    ↑(s * t) +ˢ stabilizer α (↑(s * t) : Set α)
  have that : ↥(stabilizer α (↑(s * t) : Set α)) = ↥(s * t).mulStab := by
    rw [← SetLike.coe_sort_coe, ← coe_mulStab (hs.mul ht), Finset.coe_sort_coe]
  have temp := this.trans <| (Equiv.cast that).prodCongr (Equiv.refl _)
  rw [preimage_image_quotientMk_mulStabilizer] at temp
  simpa [-coe_mul] using Fintype.card_congr temp
end Finset
