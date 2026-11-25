-- Prove2me | solution 1 for Galvin.hasKernels_arc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:03:41.731796+00:00
-- url     : https://prove2.me/submissions/3d500443-eb42-4588-b0e3-d161d356bbca

module
public import Definitions.Def_GalvinLib_GaleShapley
public import Definitions.Def_GalvinLib_Kernel
public import Mathlib.Order.Interval.Finset.Fin
public import Definitions.Def_GalvinLib_Orientation
public import Theorems.Thm_Galvin_eq_of_ends
public import Theorems.Thm_Galvin_lineGraph_adj_iff_ends
public import Theorems.Thm_Galvin_rankA_ends
public import Theorems.Thm_Galvin_rankB_ends
public import Theorems.Thm_Galvin_rankA_injective
public import Theorems.Thm_Galvin_rankB_injective
public import Theorems.Thm_Galvin_exists_isStable


set_option autoImplicit true
@[expose] public section
public section
open Galvin
open Finset SimpleGraph
variable {V : Type*} {G : SimpleGraph V}
namespace Galvin
theorem _root_.solution [Finite V] (c : G.Coloring (Fin 2)) {Δ : ℕ}
    (φ : G.lineGraph.Coloring (Fin Δ)) : HasKernels G.lineGraph (arc c φ) := by
  classical
  intro S
  obtain ⟨N, ⟨eqv⟩⟩ := Finite.exists_equiv_fin V
  let idx : V → ℕ := fun v => (eqv v : ℕ)
  have hidx : Function.Injective idx := fun a b h => eqv.injective (Fin.ext h)
  let E : V → V → Prop := fun m w => ∃ e ∈ S, endA c e = m ∧ endB c e = w
  obtain ⟨μ, hsub, hm, hw, hst⟩ := exists_isStable (rankA c φ idx) (rankB c φ idx)
    (rankA_injective c φ hidx) (rankB_injective c φ hidx) _ E rfl
  refine ⟨S.filter (fun e => μ (endA c e) (endB c e)), filter_subset _ _, ?_, ?_⟩
  · intro x hx y hy hxy
    simp only [mem_filter] at hx hy
    obtain ⟨hne, h | h⟩ := (lineGraph_adj_iff_ends c).1 hxy
    · rw [h] at hx
      exact hne (eq_of_ends c h (hm _ _ _ hx.2 hy.2))
    · rw [h] at hx
      exact hne (eq_of_ends c (hw _ _ _ hx.2 hy.2) h)
  · intro x hxS hxK
    simp only [mem_filter, hxS, true_and] at hxK
    rcases hst _ _ ⟨x, hxS, rfl, rfl⟩ hxK with ⟨w', hμ, hlt⟩ | ⟨m', hμ, hlt⟩
    · obtain ⟨f, hfS, hfA, hfB⟩ := hsub _ _ hμ
      subst hfB
      rw [← hfA] at hμ hlt
      refine ⟨f, mem_filter.2 ⟨hfS, hμ⟩, Or.inl ⟨hfA.symm, ?_⟩⟩
      rw [rankA_ends, hfA, rankA_ends] at hlt
      exact hlt
    · obtain ⟨f, hfS, hfA, hfB⟩ := hsub _ _ hμ
      subst hfA
      rw [← hfB] at hμ hlt
      refine ⟨f, mem_filter.2 ⟨hfS, hμ⟩, Or.inr ⟨hfB.symm, ?_⟩⟩
      rw [rankB_ends, hfB, rankB_ends] at hlt
      have := (φ f).isLt
      have := (φ x).isLt
      change (φ x : ℕ) < φ f
      omega
end Galvin
