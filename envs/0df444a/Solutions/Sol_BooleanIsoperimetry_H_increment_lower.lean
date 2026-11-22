-- Prove2me | solution 1 for BooleanIsoperimetry.H_increment_lower
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:37:31.574822+00:00
-- url     : https://prove2.me/submissions/99da003e-0759-4da4-991b-b274cb49c664

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cube
public import Mathlib.Algebra.BigOperators.Module
public import Mathlib.Data.Nat.Choose.Sum
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cascade
public import Theorems.Thm_BooleanIsoperimetry_H_eq_gShift_count
public import Theorems.Thm_BooleanIsoperimetry_H_one
public import Theorems.Thm_BooleanIsoperimetry_rank_add_min_ge
public import Theorems.Thm_BooleanIsoperimetry_H_zero
public import Theorems.Thm_BooleanIsoperimetry_mem_neighborhood_iff
public import Theorems.Thm_BooleanIsoperimetry_rank_image_eq
attribute [local simp] BooleanIsoperimetry.mem_neighborhood_iff



set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution (n p : ℕ) (hp : p + 1 ≤ 2 ^ n) :
    H n p + n ≤ H n (p + 1) + p := by
  obtain ⟨w, hw⟩ : ∃ w : Cube n, rank w = p := by
    have := rank_image_eq (n := n)
    exact Finset.mem_image.mp (this.symm ▸ Finset.mem_range.mpr (Nat.lt_of_succ_le hp)) |>
      Exists.imp fun x hx => hx.2
  -- Consider two cases: `w` is nonempty or `w` is empty.
  by_cases hw_nonempty : w.Nonempty
  · -- If `w` is nonempty, then `gShift⁻¹(w)` contains the `n - p` vertices
    -- `w ∪ {j}` for `j` below `w.min'`.
    have h_inv_w :
        Finset.card (Finset.filter (fun v => gShift v = w)
          (Finset.univ : Finset (Cube n))) ≥ n - p := by
      have h_inv_w : Finset.card (Finset.image (fun j => insert j w)
          (Finset.filter (fun j => (j : ℕ) < w.min' hw_nonempty)
            (Finset.univ : Finset (Fin n)))) ≥ n - p := by
        rw [Finset.card_image_of_injOn]
        · have := rank_add_min_ge w hw_nonempty
          simp_all only [Order.add_one_le_iff, Fin.val_fin_lt, Finset.lt_min'_iff, ge_iff_le,
            tsub_le_iff_right]
          rw [show Finset.filter (fun j => ∀ y ∈ w, j < y) Finset.univ =
              Finset.Iio (Finset.min' w hw_nonempty) from ?_]
          · simp +arith +decide at *; linarith
          · ext; simp [Finset.mem_Iio]
        · intro x hx y hy; simp_all +decide [Fin.ext_iff, Finset.ext_iff]
          grind +extAll
      refine le_trans h_inv_w <| Finset.card_le_card ?_
      intro v hv
      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
        Fin.val_fin_lt] at hv
      obtain ⟨a, ha, rfl⟩ := hv
      have ha_lt : ∀ y ∈ w, a < y := fun y hy => lt_of_lt_of_le ha (Finset.min'_le w y hy)
      have ha_notMem : a ∉ w := fun h => absurd (ha_lt a h) (lt_irrefl a)
      have hmin : (insert a w).min' (Finset.insert_nonempty a w) = a :=
        le_antisymm (Finset.min'_le _ _ (Finset.mem_insert_self a w))
          (Finset.le_min' _ _ _ fun y hy =>
            (Finset.mem_insert.mp hy).elim ge_of_eq fun hy => (ha_lt y hy).le)
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      unfold gShift
      rw [dif_pos (Finset.insert_nonempty a w), hmin, Finset.erase_insert ha_notMem]
    -- Since `gShift⁻¹(w)` is a subset of `filter (rank (gShift ·) = p)`, we have
    -- `H n (p + 1) ≥ H n p + |gShift⁻¹(w)|`.
    have h_filter :
        Finset.card (Finset.filter (fun v => rank (gShift v) < p + 1)
            (Finset.univ : Finset (Cube n))) ≥
          Finset.card (Finset.filter (fun v => rank (gShift v) < p)
              (Finset.univ : Finset (Cube n))) +
            Finset.card (Finset.filter (fun v => gShift v = w)
              (Finset.univ : Finset (Cube n))) := by
      rw [← Finset.card_union_of_disjoint]
      · refine Finset.card_le_card ?_
        grind
      · exact Finset.disjoint_left.mpr fun x hx₁ hx₂ => by aesop
    rw [H_eq_gShift_count, H_eq_gShift_count]
    omega
  · -- Since `w` is empty, we have `p = 0`.
    have hp_zero : p = 0 := by
      rw [← hw, show w = ∅ by aesop]; simp +decide [rank]
      simp +decide only [simplicialLt, not_and, not_not]
      simp +decide [simplicialLe]
    simp_all +decide only [zero_add, Finset.not_nonempty_iff_eq_empty, H_one, add_zero, ge_iff_le]
    rw [H_zero]; linarith
end BooleanIsoperimetry
