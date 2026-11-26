-- Prove2me | solution 1 for Finset.card_mulStab_mul_card_image_coe
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:58:39.894798+00:00
-- url     : https://prove2.me/submissions/9d1daa91-2860-4c95-8bb5-008e59559031

module
public import Mathlib.Algebra.Pointwise.Stabilizer
public import Mathlib.GroupTheory.Coset.Card
public import Mathlib.GroupTheory.GroupAction.Blocks
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Definitions.Def_Erdos338_Kneser_MulStab
public import Theorems.Thm_Finset_card_mulStab_dvd_card_mulStab
public import Theorems.Thm_P2M_Finset_card_mulStab_mul_card_image_coe__56c0b835d7e6
public import Theorems.Thm_Finset_card_mul_card_eq_mulStab_card_mul_coe

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
    #(s * t).mulStab *
      #((s +ₛ stabilizer α (↑(s * t) : Set α)) * (t +ₛ stabilizer α (↑(s * t) : Set α))) =
        #(s * t) := by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · simp
  obtain rfl | ht := t.eq_empty_or_nonempty
  · simp
  let this := QuotientGroup.preimageMkEquivSubgroupProdSet (stabilizer α (↑(s * t) : Set α))
    ((s +ˢ stabilizer α (↑(s * t) : Set α)) * (t +ˢ stabilizer α (↑(s * t) : Set α)))
  have image_coe_mul :
    ((↑(s * t) : Set α) +ˢ stabilizer α (↑(s * t) : Set α)) =
      (s +ˢ stabilizer α (↑(s * t) : Set α)) * (t +ˢ stabilizer α (↑(s * t) : Set α)) := by
    simpa [coe_mul] using Set.image_mul (QuotientGroup.mk' (stabilizer α (↑(s * t) : Set α)))
  rw [← image_coe_mul, preimage_image_quotientMk_mulStabilizer, image_coe_mul] at this
  have that :
    (stabilizer α (↑(s * t) : Set α) ×
      ↥((s +ˢ stabilizer α (↑(s * t) : Set α)) * (t +ˢ stabilizer α (↑(s * t) : Set α)))) =
      ((s * t).mulStab ×
        ↥((s +ˢ stabilizer α (↑(s * t) : Set α)) * (t +ˢ stabilizer α (↑(s * t) : Set α)))) := by
    rw [← SetLike.coe_sort_coe, ← coe_mulStab (hs.mul ht), Finset.coe_sort_coe]
  let temp := this.trans (Equiv.cast that)
  replace temp := Fintype.card_congr temp
  simp only [Fintype.card_prod, Fintype.card_coe] at temp
  have h1 : Fintype.card ((s * t : Finset α) : Set α) = Fintype.card (s * t) := by congr
  have h2 : (s +ˢ stabilizer α (↑(s * t) : Set α)) * (t +ˢ stabilizer α (↑(s * t) : Set α)) =
    ↑((s +ₛ stabilizer α (↑(s * t) : Set α)) * (t +ₛ stabilizer α (↑(s * t) : Set α))) := by simp
  have h3 :
    Fintype.card ((s +ˢ stabilizer α (↑(s * t) : Set α)) * (t +ˢ stabilizer α (↑(s * t) : Set α))) =
      Fintype.card ((s +ₛ stabilizer α (↑(s * t) : Set α)) *
        (t +ₛ stabilizer α (↑(s * t) : Set α))) := by
    simp_rw [h2]
    congr
  simp only [h1, h3, Fintype.card_coe] at temp
  rw [temp]
end Finset
