-- Prove2me | solution 2 for BoundaryBumping.exists_subcontinuum_meeting_frontier
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T11:07:03.617333+00:00
-- url     : https://prove2.me/submissions/8024bfe9-028b-4249-b051-487143a6f654

module
public import Mathlib.Topology.Separation.Regular
public import Definitions.Def_Sierpinski_Solution
public import Theorems.Thm_BoundaryBumping_closed_component_meets_frontier

set_option autoImplicit true
@[expose] public section
public section
open Set
open BoundaryBumping
variable {X : Type*} [TopologicalSpace X]
namespace BoundaryBumping
theorem _root_.solution [CompactSpace X] [T2Space X] [ConnectedSpace X]
    {F : Set X} (hF : IsClosed F) (hproper : F ≠ univ) {x : X} (hx : x ∈ F) :
    ∃ K : Set X, IsCompact K ∧ IsConnected K ∧ x ∈ K ∧ K ⊆ F ∧
      (K ∩ frontier F).Nonempty := by
  have : CompactSpace F := isCompact_iff_compactSpace.mp hF.isCompact
  refine ⟨connectedComponentIn F x, ?_, isConnected_connectedComponentIn_iff.mpr hx,
    mem_connectedComponentIn hx, connectedComponentIn_subset F x,
    closed_component_meets_frontier hF hproper hx⟩
  rw [connectedComponentIn_eq_image hx]
  exact isClosed_connectedComponent.isCompact.image continuous_subtype_val
end BoundaryBumping
