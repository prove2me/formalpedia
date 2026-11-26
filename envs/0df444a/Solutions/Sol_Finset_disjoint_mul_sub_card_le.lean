-- Prove2me | solution 1 for Finset.disjoint_mul_sub_card_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:59:25.910014+00:00
-- url     : https://prove2.me/submissions/ef44e458-67f3-47ab-95e7-c82744c08750

module
public import Mathlib.Algebra.Ring.Divisibility.Basic
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Linarith
public import Definitions.Def_Erdos338_Kneser_MulStab
public import Definitions.Def_Erdos338_Kneser_Kneser
public import Theorems.Thm_Finset_mulStab_mul_ssubset_mulStab
public import Theorems.Thm_Finset_mulStab_union
public import Theorems.Thm_Finset_mul_aux1
public import Theorems.Thm_Finset_disjoint_smul_mulStab

set_option autoImplicit true
@[expose] public section
public section
open Function MulAction
open scoped Pointwise
variable {α : Type*} [CommGroup α] [DecidableEq α] {s s' t t' C : Finset α} {a b : α}
open Finset
namespace Finset
theorem _root_.solution {a : α} (b : α) {s t C : Finset α} (has : a ∈ s)
    (hsC : Disjoint t (a • C.mulStab))
    (hst : (s ∩ a • C.mulStab * (t ∩ b • C.mulStab)).mulStab ⊆ C.mulStab) :
    (#C.mulStab : ℤ) -
        #(s ∩ a • C.mulStab * (s ∩ a • C.mulStab * (t ∩ b • C.mulStab)).mulStab) ≤
      #((s ∪ t) * C.mulStab) -
        #((s ∪ t) * (s ∩ a • C.mulStab * (t ∩ b • C.mulStab)).mulStab) := by
  obtain rfl | hC := C.eq_empty_or_nonempty
  · simp
  calc
    (#C.mulStab : ℤ) -
          #(s ∩ a • C.mulStab * (s ∩ a • C.mulStab * (t ∩ b • C.mulStab)).mulStab) =
        #(a • C.mulStab \
            (s ∩ a • C.mulStab * (s ∩ a • C.mulStab * (t ∩ b • C.mulStab)).mulStab)) := by
      rw [card_sdiff_of_subset
          (subset_trans (mul_subset_mul_left hst)
            (subset_trans (mul_subset_mul_right inter_subset_right) _)),
        card_smul_finset, Int.ofNat_sub]
      · apply le_trans (card_le_card (mul_subset_mul_left hst))
        apply
          le_trans (card_le_card inter_mul_subset)
            (le_of_le_of_eq (card_le_card inter_subset_right) _)
        rw [smul_mul_assoc, mulStab_mul_mulStab, card_smul_finset]
      · simp only [smul_mul_assoc, mulStab_mul_mulStab, Subset.rfl]
    _ ≤ #((s ∪ t) * C.mulStab) -
          #((s ∪ t) * (s ∩ a • C.mulStab * (t ∩ b • C.mulStab)).mulStab) := by
      rw [← Int.ofNat_sub (card_le_card (mul_subset_mul_left hst)),
        ← card_sdiff_of_subset (mul_subset_mul_left hst)]
      norm_cast
      gcongr #?_
      refine fun x hx => mem_sdiff.mpr ⟨?_, ?_⟩
      · apply smul_finset_subset_smul (mem_union_left t has) (mem_sdiff.mp hx).1
      have hx' := (mem_sdiff.mp hx).2
      contrapose hx'
      obtain ⟨y, hyst, d, hd, hxyd⟩ := mem_mul.mp hx'
      obtain ⟨c, hc, hcx⟩ := mem_smul_finset.mp (mem_sdiff.mp hx).1
      rw [← hcx, ← eq_mul_inv_iff_mul_eq] at hxyd
      have hyC : y ∈ a • C.mulStab := by
        rw [hxyd, smul_mul_assoc, smul_mem_smul_finset_iff, ← mulStab_mul_mulStab]
        apply mul_mem_mul hc ((mem_mulStab hC).mpr (inv_smul_eq_iff.mpr _))
        exact Eq.symm ((mem_mulStab hC).mp (hst hd))
      replace hyst : y ∈ s := by
        apply or_iff_not_imp_right.mp (mem_union.mp hyst)
        contrapose hsC
        exact not_disjoint_iff.mpr ⟨y, hsC, hyC⟩
      rw [eq_mul_inv_iff_mul_eq, hcx] at hxyd
      rw [← hxyd]
      exact mul_mem_mul (mem_inter.mpr ⟨hyst, hyC⟩) hd
end Finset
