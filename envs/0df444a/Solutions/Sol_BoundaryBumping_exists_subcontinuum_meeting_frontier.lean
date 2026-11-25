-- Prove2me | solution 1 for BoundaryBumping.exists_subcontinuum_meeting_frontier
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T08:57:58.467491+00:00
-- url     : https://prove2.me/submissions/0a32bbfd-aab9-404e-a424-bd4365e1ff3a

module
public import Mathlib.Topology.Separation.Regular
public import Definitions.Def_BoundaryBumping_Solution
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
