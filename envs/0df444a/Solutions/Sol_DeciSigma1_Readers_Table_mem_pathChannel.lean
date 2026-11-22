-- Prove2me | solution 1 for DeciSigma1.Readers.Table.mem_pathChannel
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:52:22.985804+00:00
-- url     : https://prove2.me/submissions/9fd853ec-f187-49fa-9d7a-2d3e354e96ca

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
open DeciSigma1 DeciSigma1.Readers
open DeciSigma1.Automata
variable {α S : Type} {k : ℕ}
open DeciSigma1.Readers.Table
variable (T : Table α S k)
variable {T}
namespace DeciSigma1.Readers.Table
theorem _root_.solution [DecidableEq α] [DecidableEq S] {p q : S} {x y : List α} {pq : S × S} :
    pq ∈ T.pathChannel p x q y ↔ ∃ a ≤ x.length, ∃ b ≤ y.length,
      y.drop b <+: x.drop a ∧ pq = (runFrom T.step p (x.take a), runFrom T.step q (y.take b)) := by
  simp only [pathChannel, Finset.mem_image, Finset.mem_filter, Finset.mem_product,
    Finset.mem_range, Nat.lt_succ_iff, Prod.exists]
  constructor
  · rintro ⟨a, b, ⟨⟨ha, hb⟩, hp⟩, rfl⟩
    exact ⟨a, ha, b, hb, hp, rfl⟩
  · rintro ⟨a, ha, b, hb, hp, rfl⟩
    exact ⟨a, b, ⟨⟨ha, hb⟩, hp⟩, rfl⟩
end DeciSigma1.Readers.Table
