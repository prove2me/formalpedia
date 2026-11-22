-- Prove2me | solution 1 for Front.schreier_rank
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:46:29.728809+00:00
-- url     : https://prove2.me/submissions/f1de43ff-0fb6-441b-bc80-1df832637367

module
public import Definitions.Def_LeanPool_NashWilliams_Combinatorics_Front_Defs
public import Mathlib.SetTheory.Ordinal.Rank
public import Mathlib.Order.Lattice.Nat
public import Definitions.Def_LeanPool_NashWilliams_Combinatorics_Front_Rank
public import Theorems.Thm_Front_IsFront_nil_mem_tree
public import Theorems.Thm_Front_exists_gt_range
public import Theorems.Thm_Front_mem_tree_schreier
public import Theorems.Thm_Front_schreier_rank_node
public import Theorems.Thm_Front_isFront_schreier
public import Theorems.Thm_Front_isInit_nil
attribute [local simp] Front.isInit_nil



set_option autoImplicit true
@[expose] public section
public section
open Set List Ordinal
universe u
noncomputable section
open Front
variable {F : Set (List ℕ)} {M : ℕ → ℕ}
namespace Front
theorem _root_.solution (hM : StrictMono M) : (isFront_schreier hM).rank = ω := by
  letI : IsWellFounded (List ℕ) (treeExt (schreier M)) :=
    ⟨(isFront_schreier hM).wellFounded_treeExt⟩
  rw [IsFront.rank, IsWellFounded.rank_eq]
  apply le_antisymm
  · apply Ordinal.iSup_le
    rintro ⟨y, hytree, -, -, hbne⟩
    have hyne : y ≠ [] := hbne.symm
    obtain ⟨a, hya⟩ : ∃ a, y.head? = some a := by
      cases y with
      | nil => exact absurd rfl hyne
      | cons c t => exact ⟨c, rfl⟩
    rw [schreier_rank_node hM hytree hya, Order.succ_eq_add_one, ← Nat.cast_add_one]
    exact le_of_lt (Ordinal.natCast_lt_omega0 _)
  · rw [← Ordinal.iSup_natCast]
    apply Ordinal.iSup_le
    intro n
    obtain ⟨x, hxM, hxgt⟩ := exists_gt_range hM n
    have hxtree : [x] ∈ tree (schreier M) := by
      refine (mem_tree_schreier hM).mpr ⟨List.pairwise_singleton _ _, ?_, ?_⟩
      · intro z hz; simp only [List.mem_singleton] at hz; subst hz; exact hxM
      · intro c hc
        rw [List.head?_cons] at hc
        obtain rfl := Option.some.inj hc
        simp only [List.length_cons, List.length_nil]; omega
    have hte : treeExt (schreier M) [x] [] :=
      ⟨hxtree, (isFront_schreier hM).nil_mem_tree, List.nil_prefix, by simp⟩
    have hrank : IsWellFounded.rank (treeExt (schreier M)) [x] = (x : Ordinal) := by
      rw [schreier_rank_node hM hxtree List.head?_cons]; simp
    calc (n : Ordinal) ≤ ((x + 1 : ℕ) : Ordinal) := by rw [Nat.cast_le]; omega
      _ = Order.succ (IsWellFounded.rank (treeExt (schreier M)) [x]) := by
            rw [hrank, Order.succ_eq_add_one, Nat.cast_add_one]
      _ ≤ _ := Ordinal.le_iSup
            (fun b : {b // treeExt (schreier M) b []} =>
              Order.succ (IsWellFounded.rank (treeExt (schreier M)) (b : List ℕ)))
            ⟨[x], hte⟩
end Front
