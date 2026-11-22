-- Prove2me | solution 1 for DeciSigma1.Holes.Fresh.mem_contextAnchors_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:47:10.737939+00:00
-- url     : https://prove2.me/submissions/7cae016f-bcc2-4045-b318-60a964b55938

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
variable [DecidableEq α]
variable (W : Fin k → List α)
namespace DeciSigma1.Holes.Fresh
theorem _root_.solution {t : ℕ} {u : List α} {e : ℕ} :
    e ∈ contextAnchors W (t + 1) u ↔
      e ≤ u.length ∧ ∃ m ∈ active W (t + 1), marker W (t + 1) m <:+ u.take e :=
  Level.mem_markerEndCuts
end DeciSigma1.Holes.Fresh
