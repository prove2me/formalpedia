-- Prove2me | solution 1 for BooleanIsoperimetry.gShift_preimage_eq_insert_below_min
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:28:59.274783+00:00
-- url     : https://prove2.me/submissions/5c40374b-c4ac-49ff-af0b-21bad11da88b

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cascade
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Macaulay
public import Theorems.Thm_BooleanIsoperimetry_mem_neighborhood_iff
attribute [local simp] BooleanIsoperimetry.mem_neighborhood_iff



set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution {n : ℕ} (w : Cube n) (h : w.Nonempty) :
    Finset.univ.filter (fun v : Cube n => gShift v = w)
      = (Finset.univ.filter (fun j : Fin n => (j : ℕ) < (w.min' h : ℕ))).image
          (fun j => insert j w) := by
  ext v
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
  constructor
  · intro hgv
    have hv : v.Nonempty := by
      by_contra hcon
      rw [Finset.not_nonempty_iff_eq_empty] at hcon
      rw [gShift, dif_neg (by rw [hcon]; exact Finset.not_nonempty_empty)] at hgv
      rw [hcon] at hgv
      exact (h.ne_empty hgv.symm)
    have hg : gShift v = v.erase (v.min' hv) := by unfold gShift; rw [dif_pos hv]
    rw [hg] at hgv
    set m := v.min' hv with hm
    refine ⟨m, ?_, ?_⟩
    · -- (m : ℕ) < (w.min' h : ℕ)
      have hmem : (w.min' h) ∈ w := Finset.min'_mem w h
      have hwsub : w ⊆ v := by rw [← hgv]; exact Finset.erase_subset _ _
      have hmin_le : m ≤ w.min' h := Finset.min'_le v (w.min' h) (hwsub hmem)
      have hmnotw : m ∉ w := by rw [← hgv]; exact Finset.notMem_erase _ _
      have hneq : m ≠ w.min' h := by
        intro hc
        exact hmnotw (by rw [hc]; exact hmem)
      have hlt : m < w.min' h := lt_of_le_of_ne hmin_le hneq
      exact hlt
    · -- insert m w = v
      rw [← hgv]
      exact Finset.insert_erase (Finset.min'_mem v hv)
  · rintro ⟨j, hj, rfl⟩
    have hjw : j ∉ w := by
      intro hjmem
      have := Finset.min'_le w j hjmem
      omega
    have hne : (insert j w).Nonempty := ⟨j, Finset.mem_insert_self _ _⟩
    have hmin : (insert j w).min' hne = j := by
      apply le_antisymm
      · exact Finset.min'_le _ j (Finset.mem_insert_self _ _)
      · apply Finset.le_min'
        intro y hy
        rcases Finset.mem_insert.mp hy with h1 | h1
        · rw [h1]
        · have := Finset.min'_le w y h1
          omega
    rw [gShift, dif_pos hne, hmin, Finset.erase_insert hjw]
end BooleanIsoperimetry
