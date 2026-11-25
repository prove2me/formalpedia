-- Prove2me | solution 2 for BoundaryBumping.exists_clopen_between_component_and_open
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T10:57:24.75103+00:00
-- url     : https://prove2.me/submissions/739b4f5f-5bcf-4a04-a654-a9e1b6403330

module
public import Mathlib.Topology.Separation.Regular
public import Definitions.Def_Sierpinski_Solution

set_option autoImplicit true
@[expose] public section
public section
open Set
open BoundaryBumping
variable {X : Type*} [TopologicalSpace X]
namespace BoundaryBumping
theorem _root_.solution [CompactSpace X] [T2Space X]
    (x : X) {U : Set X} (hU : IsOpen U) (hCU : connectedComponent x ⊆ U) :
    ∃ V : Set X, IsClopen V ∧ connectedComponent x ⊆ V ∧ V ⊆ U := by
  classical
  let N := {s : Set X // IsClopen s ∧ x ∈ s}
  have hdisj : Disjoint Uᶜ (⋂ s : N, (s : Set X)) := by
    rw [← connectedComponent_eq_iInter_isClopen x]
    exact disjoint_compl_left_iff_subset.mpr hCU
  obtain ⟨a, ha⟩ := hU.isClosed_compl.isCompact.elim_finite_subfamily_closed
    (fun s : N => (s : Set X)) (fun s => s.2.1.1) (Set.disjoint_iff_inter_eq_empty.mp hdisj)
  let V : Set X := ⋂ s ∈ a, (s : Set X)
  have hV : IsClopen V := isClopen_biInter_finset fun s _ => s.2.1
  have hxV : x ∈ V := mem_iInter₂.mpr fun s _ => s.2.2
  exact ⟨V, hV, hV.connectedComponent_subset hxV,
    disjoint_compl_left_iff_subset.mp (Set.disjoint_iff_inter_eq_empty.mpr ha)⟩
end BoundaryBumping
