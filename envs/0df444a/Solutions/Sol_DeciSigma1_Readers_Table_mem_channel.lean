-- Prove2me | solution 1 for DeciSigma1.Readers.Table.mem_channel
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:52:48.16405+00:00
-- url     : https://prove2.me/submissions/cfc7f9e4-eded-414d-a172-c828ee7d6198

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
public import Theorems.Thm_DeciSigma1_Readers_Table_mem_pathChannel

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Readers
open DeciSigma1.Automata
variable {α S : Type} {k : ℕ}
open DeciSigma1.Readers.Table
variable (T : Table α S k)
variable {T}
namespace DeciSigma1.Readers.Table
theorem _root_.solution [DecidableEq α] [DecidableEq S] {W : Fin k → List α} {i j : Fin k}
    {pq : S × S} :
    pq ∈ T.channel W i j ↔ ∃ a ≤ (W i).length, ∃ b ≤ (W j).length,
      (W j).drop b <+: (W i).drop a ∧ pq = (T.runPrefix W i a, T.runPrefix W j b) := mem_pathChannel
end DeciSigma1.Readers.Table
