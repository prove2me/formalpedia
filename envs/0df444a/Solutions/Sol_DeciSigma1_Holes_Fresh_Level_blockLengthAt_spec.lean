-- Prove2me | solution 1 for DeciSigma1.Holes.Fresh.Level.blockLengthAt_spec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:16:33.203838+00:00
-- url     : https://prove2.me/submissions/6ea3c641-9646-49fd-9027-6e7576ddffb7

module
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_DeciSigma1_Readers_Basic
public import Mathlib.Order.Nat
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Order.Interval.Finset.Nat
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Hierarchy
public import Theorems.Thm_DeciSigma1_Holes_Fresh_Level_mem_markerEndCuts

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Fresh
open DeciSigma1.Readers
open Finset
variable {α : Type} {k : ℕ}
open DeciSigma1.Holes.Fresh.Level
variable [DecidableEq α] (L : Level α k)
variable {L}
namespace DeciSigma1.Holes.Fresh.Level
theorem _root_.solution {x : List α} {e : ℕ} (he : e ∈ L.markerEndCuts x) :
    ∃ m ∈ L.active, L.marker m <:+ x.take e ∧ L.blockLengthAt x e = (L.marker m).length := by
  have hne : (L.active.filter (fun m => L.marker m <:+ x.take e)).Nonempty := by
    obtain ⟨-, m, hm, hs⟩ := mem_markerEndCuts.mp he
    exact ⟨m, mem_filter.mpr ⟨hm, hs⟩⟩
  obtain ⟨m, hm, hsup⟩ := exists_mem_eq_sup _ hne (fun m => (L.marker m).length)
  rw [mem_filter] at hm
  exact ⟨m, hm.1, hm.2, hsup⟩
end DeciSigma1.Holes.Fresh.Level
