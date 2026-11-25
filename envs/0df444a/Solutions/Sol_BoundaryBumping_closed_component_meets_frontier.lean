-- Prove2me | solution 1 for BoundaryBumping.closed_component_meets_frontier
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T08:54:58.749735+00:00
-- url     : https://prove2.me/submissions/dd24a161-d0c4-4bf2-892c-caaf51c23555

module
public import Mathlib.Topology.Separation.Regular
public import Definitions.Def_BoundaryBumping_Solution
public import Theorems.Thm_BoundaryBumping_exists_clopen_between_component_and_open
section
@[expose] public section
open Set
namespace BoundaryBumping
variable {X : Type*} [TopologicalSpace X]
private theorem clopen_image_of_subset_interior {F : Set X} (hF : IsClosed F)
    {V : Set F} (hV : IsClopen V)
    (hVF : Subtype.val '' V ⊆ interior F) : IsClopen (Subtype.val '' V) := by
  refine ⟨hF.isClosedEmbedding_subtypeVal.isClosed_iff_image_isClosed.mp hV.1, ?_⟩
  obtain ⟨O, hO, hpre⟩ := isOpen_induced_iff.mp hV.2
  have hOV : Subtype.val '' V = O ∩ F := by
    rw [← hpre, Subtype.image_preimage_coe, inter_comm]
  have hEq : Subtype.val '' V = O ∩ interior F := by
    apply Subset.antisymm
    · intro y hy
      exact ⟨(hOV ▸ hy).1, hVF hy⟩
    · intro y hy
      rw [hOV]
      exact ⟨hy.1, interior_subset hy.2⟩
  rw [hEq]
  exact hO.inter isOpen_interior
end BoundaryBumping
end
end

set_option autoImplicit true
@[expose] public section
public section
open Set
open BoundaryBumping
variable {X : Type*} [TopologicalSpace X]
namespace BoundaryBumping
theorem _root_.solution [CompactSpace X] [T2Space X] [ConnectedSpace X]
    {F : Set X} (hF : IsClosed F) (hproper : F ≠ univ) {x : X} (hx : x ∈ F) :
    (connectedComponentIn F x ∩ frontier F).Nonempty := by
  classical
  by_contra hmiss
  have hCI : connectedComponentIn F x ⊆ interior F := by
    intro y hy
    by_contra hyI
    apply hmiss
    exact ⟨y, hy, by
      rw [frontier, hF.closure_eq]
      exact ⟨connectedComponentIn_subset F x hy, hyI⟩⟩
  have : CompactSpace F := isCompact_iff_compactSpace.mp hF.isCompact
  let p : F := ⟨x, hx⟩
  obtain ⟨V, hV, hCV, hVI⟩ := exists_clopen_between_component_and_open p
    (isOpen_interior.preimage continuous_subtype_val) (by
      intro y hy
      exact hCI (by rw [connectedComponentIn_eq_image hx]; exact ⟨y, hy, rfl⟩))
  have hImage : IsClopen (Subtype.val '' V : Set X) :=
    clopen_image_of_subset_interior hF hV (by
      rintro _ ⟨y, hy, rfl⟩
      exact hVI hy)
  have hxImage : x ∈ (Subtype.val '' V : Set X) :=
    ⟨p, hCV mem_connectedComponent, rfl⟩
  apply hproper
  apply Subset.antisymm (subset_univ F)
  intro y _
  have hy : y ∈ (Subtype.val '' V : Set X) := by
    rw [hImage.eq_univ ⟨x, hxImage⟩]
    trivial
  rcases hy with ⟨z, _, rfl⟩
  exact z.2
end BoundaryBumping
