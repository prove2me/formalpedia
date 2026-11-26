-- Prove2me | solution 1 for ExponentialJuliaSetMisiurewicz.IsPreconnected.inter_frontier_nonempty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:05:03.859789+00:00
-- url     : https://prove2.me/submissions/6b7abfd0-2fe0-41bf-9a9b-f8f7000b9567

import Mathlib.Order.CompletePartialOrder
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.OpenMapping
import Mathlib.Data.Nat.Nth
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Definitions.Def_ExpChaotic_Expansion
import Definitions.Def_ExpChaotic_StripGeometry

set_option autoImplicit true
open Function Filter Set Metric
open scoped Topology NNReal Uniformity
open ExponentialJuliaSetMisiurewicz
noncomputable section
namespace ExponentialJuliaSetMisiurewicz
namespace IsPreconnected
theorem _root_.solution
    {X : Type*} [TopologicalSpace X] {u v : Set X}
    (hv : IsPreconnected v) (h1 : (v ∩ u).Nonempty) (h2 : (v \ u).Nonempty) :
    (v ∩ frontier u).Nonempty := by
  by_contra hcon
  rw [Set.not_nonempty_iff_eq_empty] at hcon
  have hnofr : ∀ x ∈ v, x ∉ frontier u := by
    intro x hx hfr
    exact absurd (Set.mem_inter hx hfr) (by rw [hcon]; exact Set.notMem_empty x)
  have hcover : v ⊆ interior u ∪ interior uᶜ := by
    intro x hx
    by_cases hi : x ∈ interior u
    · exact Or.inl hi
    refine Or.inr ?_
    rw [interior_compl, Set.mem_compl_iff]
    intro hcl
    exact hnofr x hx ⟨hcl, hi⟩
  have hmem1 : (v ∩ interior u).Nonempty := by
    obtain ⟨x, hxv, hxu⟩ := h1
    refine ⟨x, hxv, ?_⟩
    by_contra hi
    exact hnofr x hxv ⟨subset_closure hxu, hi⟩
  have hmem2 : (v ∩ interior uᶜ).Nonempty := by
    obtain ⟨x, hxv, hxu⟩ := h2
    refine ⟨x, hxv, ?_⟩
    rw [interior_compl, Set.mem_compl_iff]
    intro hcl
    exact hnofr x hxv ⟨hcl, fun hi => hxu (interior_subset hi)⟩
  obtain ⟨x, hxv, hx1, hx2⟩ :=
    hv (interior u) (interior uᶜ) isOpen_interior isOpen_interior hcover hmem1 hmem2
  exact (interior_subset hx2) (interior_subset hx1)
end IsPreconnected
end ExponentialJuliaSetMisiurewicz
