-- Prove2me | solution 1 for Front.exists_extend_gt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:43:54.912743+00:00
-- url     : https://prove2.me/submissions/91770eac-d357-4498-8216-0c2c2b0b9bda

module
public import Definitions.Def_LeanPool_NashWilliams_Combinatorics_Front_Defs
public import Mathlib.SetTheory.Ordinal.Rank
public import Mathlib.Order.Lattice.Nat
public import Definitions.Def_LeanPool_NashWilliams_Combinatorics_Front_Rank
public import Theorems.Thm_Front_exists_gt_range

set_option autoImplicit true
@[expose] public section
public section
open Set List Ordinal
universe u
noncomputable section
open Front
variable {F : Set (List ℕ)} {M : ℕ → ℕ}
namespace Front
theorem _root_.solution (hM : StrictMono M) (s : List ℕ) :
    ∃ x ∈ Set.range M, ∀ y ∈ s, y < x := by
  obtain ⟨x, hx, hlt⟩ := exists_gt_range hM (s.toFinset.sup id)
  refine ⟨x, hx, fun y hy => ?_⟩
  exact lt_of_le_of_lt (Finset.le_sup (f := id) (List.mem_toFinset.mpr hy)) hlt
end Front
