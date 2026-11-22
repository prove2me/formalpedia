-- Prove2me | solution 1 for Front.IsFront.shrink_rank_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:44:29.403178+00:00
-- url     : https://prove2.me/submissions/c896c6ec-cab9-4cbf-86af-32f75b2ba9f9

module
public import Definitions.Def_LeanPool_NashWilliams_Combinatorics_Front_Rank
public import Definitions.Def_LeanPool_NashWilliams_Combinatorics_Front_Shrink
public import Theorems.Thm_Front_tree_shrink_subset
public import Theorems.Thm_RelHom_rank_le


set_option autoImplicit true
@[expose] public section
public section
open Set List
noncomputable section
open Front
variable {F : Set (List ℕ)} {M : ℕ → ℕ}
namespace Front
namespace IsFront
theorem _root_.solution (hF : IsFront F M) {E : ℕ → ℕ} (hE : StrictMono E) :
    (shrink_isFront hF hE).rank ≤ hF.rank := by
  letI : IsWellFounded (List ℕ) (treeExt F) := ⟨hF.wellFounded_treeExt⟩
  letI : IsWellFounded (List ℕ) (treeExt (shrink F (M ∘ E))) :=
    ⟨(shrink_isFront hF hE).wellFounded_treeExt⟩
  -- The identity is a relation homomorphism `treeExt (shrink F N) →r treeExt F`.
  let φ : treeExt (shrink F (M ∘ E)) →r treeExt F :=
    ⟨id, by
      rintro x y ⟨hx, hy, hyx, hne⟩
      exact ⟨tree_shrink_subset hx, tree_shrink_subset hy, hyx, hne⟩⟩
  change IsWellFounded.rank (treeExt (shrink F (M ∘ E))) [] ≤ IsWellFounded.rank (treeExt F) []
  exact φ.rank_le []
end IsFront
end Front
