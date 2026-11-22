-- Prove2me | solution 1 for Front.IsFront.ray_rank_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:44:39.706448+00:00
-- url     : https://prove2.me/submissions/49e1bbb7-039f-4160-ae97-612369a92362

module
public import Definitions.Def_LeanPool_NashWilliams_Combinatorics_Front_Rank
public import Mathlib.Order.Lattice.Nat
public import Definitions.Def_LeanPool_NashWilliams_Combinatorics_Front_Ray
public import Theorems.Thm_Front_mem_tree_ray
public import Theorems.Thm_Front_IsFront_nil_mem_tree
public import Theorems.Thm_RelHom_rank_le


set_option autoImplicit true
@[expose] public section
public section
open Set List
noncomputable section
variable {M : ℕ → ℕ}
open Front
variable {F : Set (List ℕ)}
namespace Front
namespace IsFront
theorem _root_.solution (hF : IsFront F M) (h0 : [] ∉ F) {n : ℕ}
    (hn : n ∈ Set.range M) : (hF.ray_isFront_mem h0 hn).rank < hF.rank := by
  have ha : [n] ∈ tree F := hF.singleton_mem_tree h0 hn
  letI : IsWellFounded (List ℕ) (treeExt F) := ⟨hF.wellFounded_treeExt⟩
  letI : IsWellFounded (List ℕ) (treeExt (ray F n)) :=
    ⟨(hF.ray_isFront_mem h0 hn).wellFounded_treeExt⟩
  -- The head-attaching map `t ↦ n :: t` is a relation homomorphism into `treeExt F`.
  let φ : treeExt (ray F n) →r treeExt F :=
    ⟨fun t => n :: t, by
      rintro x y ⟨hx, hy, hyx, hne⟩
      refine ⟨mem_tree_ray.mp hx, mem_tree_ray.mp hy, (List.prefix_cons_inj n).mpr hyx, ?_⟩
      intro hc; injection hc with _ h; exact hne h⟩
  have hle : IsWellFounded.rank (treeExt (ray F n)) [] ≤ IsWellFounded.rank (treeExt F) [n] :=
    φ.rank_le []
  have hlt : IsWellFounded.rank (treeExt F) [n] < IsWellFounded.rank (treeExt F) [] :=
    IsWellFounded.rank_lt_of_rel
      ⟨ha, hF.nil_mem_tree, List.nil_prefix, (List.cons_ne_nil n []).symm⟩
  change IsWellFounded.rank (treeExt (ray F n)) [] < IsWellFounded.rank (treeExt F) []
  exact lt_of_le_of_lt hle hlt
end IsFront
end Front
