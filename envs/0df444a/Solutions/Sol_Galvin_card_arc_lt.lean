-- Prove2me | solution 1 for Galvin.card_arc_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:56:54.683601+00:00
-- url     : https://prove2.me/submissions/96021872-2dee-4c70-8c55-cfb5dae3738d

module
public import Definitions.Def_GalvinLib_GaleShapley
public import Definitions.Def_GalvinLib_Kernel
public import Mathlib.Order.Interval.Finset.Fin
public import Definitions.Def_GalvinLib_Orientation
public import Theorems.Thm_Galvin_eq_of_colour_eq

set_option autoImplicit true
@[expose] public section
public section
open Galvin
open Finset SimpleGraph
variable {V : Type*} {G : SimpleGraph V}
namespace Galvin
theorem _root_.solution [Fintype G.edgeSet] (c : G.Coloring (Fin 2)) {Δ : ℕ}
    (φ : G.lineGraph.Coloring (Fin Δ)) (e : G.edgeSet) [DecidablePred (arc c φ e)] :
    (univ.filter (arc c φ e)).card < Δ := by
  classical
  have hsub : univ.filter (arc c φ e) ⊆
      univ.filter (fun f => endA c e = endA c f ∧ φ f < φ e) ∪
        univ.filter (fun f => endB c e = endB c f ∧ φ e < φ f) := by
    intro f hf
    simp only [arc, mem_filter, mem_univ, true_and, mem_union] at hf ⊢
    exact hf
  have h1 : (univ.filter (fun f => endA c e = endA c f ∧ φ f < φ e)).card ≤
      (Iio (φ e)).card := by
    refine card_le_card_of_injOn (fun f => φ f) (fun f hf => ?_) (fun f hf f' hf' h => ?_)
    · simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hf
      simpa using hf.2
    · simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hf hf'
      exact eq_of_colour_eq c φ h (Or.inl (hf.1.symm.trans hf'.1))
  have h2 : (univ.filter (fun f => endB c e = endB c f ∧ φ e < φ f)).card ≤
      (Ioi (φ e)).card := by
    refine card_le_card_of_injOn (fun f => φ f) (fun f hf => ?_) (fun f hf f' hf' h => ?_)
    · simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hf
      simpa using hf.2
    · simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hf hf'
      exact eq_of_colour_eq c φ h (Or.inr (hf.1.symm.trans hf'.1))
  rw [Fin.card_Iio] at h1
  rw [Fin.card_Ioi] at h2
  have h3 := (card_le_card hsub).trans (card_union_le _ _)
  have h4 := (φ e).isLt
  omega
end Galvin
