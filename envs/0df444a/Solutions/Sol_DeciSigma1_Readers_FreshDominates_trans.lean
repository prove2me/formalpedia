-- Prove2me | solution 1 for DeciSigma1.Readers.FreshDominates.trans
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:42:47.522025+00:00
-- url     : https://prove2.me/submissions/ce7d2674-dc22-4edf-820f-ae5d42912395

module
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_DeciSigma1_Automata_Basic
public import Mathlib.Order.Nat
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Pigeonhole
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Tactic.Linarith
public import Mathlib.Data.Finset.Prod
public import Definitions.Def_LeanPool_DeciSigma1_Readers_Basic
public import Theorems.Thm_DeciSigma1_Readers_Dominates_trans

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Readers
open DeciSigma1.Automata
variable {α S : Type} {k : ℕ}
open Table
variable [DecidableEq α] [DecidableEq S]
variable {T : Table α S k} {U V W : Fin k → List α}
namespace DeciSigma1.Readers
namespace FreshDominates
theorem _root_.solution (h₁ : FreshDominates T U V) (h₂ : FreshDominates T V W) :
    FreshDominates T U W :=
  ⟨h₁.1.trans h₂.1, h₁.2⟩
end FreshDominates
end DeciSigma1.Readers
