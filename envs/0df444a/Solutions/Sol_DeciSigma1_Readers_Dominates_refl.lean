-- Prove2me | solution 1 for DeciSigma1.Readers.Dominates.refl
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:46:26.772026+00:00
-- url     : https://prove2.me/submissions/600ef1ee-42cc-4216-b712-1eacb6b667d3

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
namespace Dominates
theorem _root_.solution (T : Table α S k) (W : Fin k → List α) : Dominates T W W :=
  ⟨fun _ => rfl, fun _ => Finset.Subset.refl _, fun _ _ => Finset.Subset.refl _⟩
end Dominates
end DeciSigma1.Readers
