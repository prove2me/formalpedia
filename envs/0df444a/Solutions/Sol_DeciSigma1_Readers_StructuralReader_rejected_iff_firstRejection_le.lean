-- Prove2me | solution 1 for DeciSigma1.Readers.StructuralReader.rejected_iff_firstRejection_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:14:06.173458+00:00
-- url     : https://prove2.me/submissions/0c2173a3-3ffd-4432-a025-cf2ef4424c0b

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
public import Theorems.Thm_DeciSigma1_Readers_StructuralReader_firstRejection_spec
public import Theorems.Thm_DeciSigma1_Readers_StructuralReader_rejected_of_firstRejection_le

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Readers
open DeciSigma1.Automata
variable {α S : Type} {k : ℕ}
open Table
open DeciSigma1.Readers.StructuralReader
variable (M : StructuralReader α S k)
variable {M}
namespace DeciSigma1.Readers.StructuralReader
theorem _root_.solution {W : Fin k → List α} {i : Fin k} {a : ℕ} (h : M.Eligible W i)
    (h2 : a ≤ (W i).length) : M.rejected (M.runPrefix W i a) = true ↔ M.firstRejection W i ≤ a := by
  constructor
  · intro hr
    by_contra hlt
    rw [(firstRejection_spec h).2.2 a (by omega)] at hr
    exact Bool.false_ne_true hr
  · exact fun h1 => rejected_of_firstRejection_le h h1 h2
end DeciSigma1.Readers.StructuralReader
