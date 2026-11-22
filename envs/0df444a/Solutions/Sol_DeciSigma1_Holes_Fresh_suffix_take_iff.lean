-- Prove2me | solution 1 for DeciSigma1.Holes.Fresh.suffix_take_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:43:42.301553+00:00
-- url     : https://prove2.me/submissions/d6c753a8-0155-4dd9-8a88-421e757b7447

module
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_DeciSigma1_Readers_Basic
public import Mathlib.Order.Nat
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Order.Interval.Finset.Nat
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Hierarchy
public import Theorems.Thm_DeciSigma1_Automata_mem_wordsUpTo
public import Theorems.Thm_DeciSigma1_runFrom_cons
public import Theorems.Thm_DeciSigma1_runFrom_nil
public import Theorems.Thm_DeciSigma1_runFrom_snoc
attribute [local simp] DeciSigma1.Automata.mem_wordsUpTo
attribute [local simp] DeciSigma1.runFrom_cons
attribute [local simp] DeciSigma1.runFrom_nil
attribute [local simp] DeciSigma1.runFrom_snoc



set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Fresh
open DeciSigma1.Readers
open Finset
variable {α : Type} {k : ℕ}
variable {x u v : List α}
namespace DeciSigma1.Holes.Fresh
theorem _root_.solution {e : ℕ} (he : e ≤ x.length) :
    u <:+ x.take e ↔ u.length ≤ e ∧ u <+: x.drop (e - u.length) := by
  have hte : (x.take e).length = e := by simp [Nat.min_eq_left he]
  constructor
  · rintro ⟨s, hs⟩
    have hsl : s.length + u.length = e := by rw [← hte, ← hs, List.length_append]
    refine ⟨by omega, x.drop e, ?_⟩
    have hx : x = s ++ (u ++ x.drop e) := by
      rw [← List.append_assoc, hs, List.take_append_drop]
    rw [show e - u.length = s.length by omega]
    conv_rhs => rw [hx]
    rw [List.drop_left]
  · rintro ⟨hl, r, hr⟩
    refine ⟨x.take (e - u.length), ?_⟩
    have : x.take e = x.take (e - u.length) ++ (x.drop (e - u.length)).take u.length := by
      rw [← List.take_add, Nat.sub_add_cancel hl]
    rw [this, ← hr, List.take_left]
end DeciSigma1.Holes.Fresh
