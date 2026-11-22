-- Prove2me | solution 1 for DeciSigma1.Holes.Fresh.card_anchors_Ioc_marker_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:31:36.01296+00:00
-- url     : https://prove2.me/submissions/19e418c4-777f-42fe-a031-040e2071144b

module
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_DeciSigma1_Readers_Basic
public import Mathlib.Order.Nat
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Order.Interval.Finset.Nat
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Hierarchy
public import Theorems.Thm_DeciSigma1_Holes_Fresh_card_anchors_inside_marker_le

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Fresh
open DeciSigma1.Readers
open Finset
variable {α : Type} {k : ℕ}
variable [DecidableEq α]
open DeciSigma1.Readers.Table
variable {S : Type} [Fintype S] [DecidableEq S]
namespace DeciSigma1.Holes.Fresh
theorem _root_.solution {T : Table α S k} {W : Fin k → List α}
    (hfr : ∀ i, T.Fresh W i) (t : ℕ) {l : Fin k} (hl : l ∈ active W (t + 1))
    (ctx : List α) {a : ℕ} (hocc : marker W (t + 1) l <+: ctx.drop a) :
    ((contextAnchors W t ctx).filter
        (fun p => a < p ∧ p ≤ a + (marker W (t + 1) l).length)).card ≤
      k * (Fintype.card S - 1) + 2 := by
  have hsub : (contextAnchors W t ctx).filter
        (fun p => a < p ∧ p ≤ a + (marker W (t + 1) l).length) ⊆
      insert (a + (marker W (t + 1) l).length) ((contextAnchors W t ctx).filter
        (fun p => a < p ∧ p < a + (marker W (t + 1) l).length)) := by
    intro p hp
    rw [mem_filter] at hp
    rw [mem_insert, mem_filter]
    rcases lt_or_eq_of_le hp.2.2 with h | h
    · exact Or.inr ⟨hp.1, hp.2.1, h⟩
    · exact Or.inl h
  have := card_anchors_inside_marker_le hfr t hl ctx hocc
  have := card_le_card hsub
  have := card_insert_le (a + (marker W (t + 1) l).length) ((contextAnchors W t ctx).filter
        (fun p => a < p ∧ p < a + (marker W (t + 1) l).length))
  omega
end DeciSigma1.Holes.Fresh
