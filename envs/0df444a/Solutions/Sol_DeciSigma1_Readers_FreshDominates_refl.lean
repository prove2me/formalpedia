-- Prove2me | solution 1 for DeciSigma1.Readers.FreshDominates.refl
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:47:54.195797+00:00
-- url     : https://prove2.me/submissions/aa213943-8e44-409e-a697-aadc1e7c12b6

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
public import Theorems.Thm_DeciSigma1_Readers_Dominates_refl

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
theorem _root_.solution (hW : ∀ i, T.Fresh W i) :
    FreshDominates T W W := ⟨Dominates.refl T W, hW⟩
end FreshDominates
end DeciSigma1.Readers
