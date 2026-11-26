-- Prove2me | solution 1 for Finset.mulStab_union
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:58:04.080979+00:00
-- url     : https://prove2.me/submissions/e34851e3-4fde-4ac3-bdb8-740208f59a16

module
public import Mathlib.Algebra.Ring.Divisibility.Basic
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Linarith
public import Definitions.Def_Erdos338_Kneser_MulStab
public import Definitions.Def_Erdos338_Kneser_Kneser
public import Theorems.Thm_Finset_mulStab_mul_ssubset_mulStab

set_option autoImplicit true
@[expose] public section
public section
open Function MulAction
open scoped Pointwise
variable {α : Type*} [CommGroup α] [DecidableEq α] {s s' t t' C : Finset α} {a b : α}
open Finset
namespace Finset
theorem _root_.solution (hs₁ : (s ∩ a • C.mulStab).Nonempty) (ht₁ : (t ∩ b • C.mulStab).Nonempty)
    (hab : ¬(a * b) • C.mulStab ⊆ s * t)
    (hC : Disjoint C (s ∩ a • C.mulStab * (t ∩ b • C.mulStab))) :
    (C ∪ s ∩ a • C.mulStab * (t ∩ b • C.mulStab)).mulStab =
      (s ∩ a • C.mulStab * (t ∩ b • C.mulStab)).mulStab := by
  obtain rfl | hCne := C.eq_empty_or_nonempty
  · simp
  refine
    ((subset_inter (mulStab_mul_ssubset_mulStab hs₁ ht₁ hab).subset Subset.rfl).trans
          inter_mulStab_subset_mulStab_union).antisymm'
      fun x hx => ?_
  replace hx := (mem_mulStab <| (hs₁.mul ht₁).mono subset_union_right).mp hx
  rw [smul_finset_union] at hx
  suffices hxC : x ∈ C.mulStab by
    rw [(mem_mulStab hCne).mp hxC] at hx
    rw [mem_mulStab_iff_subset_smul_finset (hs₁.mul ht₁)]
    exact hC.symm.left_le_of_le_sup_left (le_sup_right.trans hx.ge)
  rw [mem_mulStab_iff_smul_finset_subset hCne]
  obtain h | h := disjoint_or_nonempty_inter (x • C) (s ∩ a • C.mulStab * (t ∩ b • C.mulStab))
  · exact h.left_le_of_le_sup_right (le_sup_left.trans_eq hx)
  have hUn :
    ((C.biUnion fun y => x • y • C.mulStab) ∩
        (s ∩ a • C.mulStab * (t ∩ b • C.mulStab))).Nonempty := by
    have : (x • C.biUnion fun y => y • C.mulStab) = C.biUnion fun y => x • y • C.mulStab :=
      biUnion_image
    simpa [← this]
  simp_rw [biUnion_inter, biUnion_nonempty, ← smul_assoc, smul_eq_mul] at hUn
  obtain ⟨y, hy, hyne⟩ := hUn
  have hxyCsubC : (x * y) • C.mulStab ⊆ x • C := by
    rw [← smul_eq_mul, smul_assoc, smul_finset_subset_smul_finset_iff]
    exact smul_finset_mulStab_subset hy
  have hxyC : Disjoint ((x * y) • C.mulStab) C := by
    convert disjoint_smul_finset_mulStab_mul_mulStab fun hxyC => _
    · exact C.mul_mulStab.symm
    rw [mul_mulStab] at hxyC
    exact hyne.not_disjoint (hC.mono_left hxyC)
  have hxysub : (x * y) • C.mulStab ⊆ s ∩ a • C.mulStab * (t ∩ b • C.mulStab) :=
    hxyC.left_le_of_le_sup_left (hxyCsubC.trans <| subset_union_left.trans hx.subset)
  suffices s ∩ a • C.mulStab * (t ∩ b • C.mulStab) ⊂ (a * b) • C.mulStab by
    have := (card_le_card hxysub).not_gt ((card_lt_card this).trans_eq ?_)
    cases this
    simp_rw [card_smul_finset]
  apply ssubset_of_subset_not_subset
  · refine (mul_subset_mul inter_subset_right inter_subset_right).trans ?_
    simp only [smul_mul_smul_comm, mulStab_mul_mulStab, subset_refl]
  · contrapose hab
    exact hab.trans (mul_subset_mul inter_subset_left inter_subset_left)
end Finset
