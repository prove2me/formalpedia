-- Prove2me | solution 1 for DeciSigma1.Readers.StructuralReader.runPrefix_ne_of_le_firstRejection
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:52:28.667967+00:00
-- url     : https://prove2.me/submissions/efb6ca88-f72d-412c-b122-63ea98aeabde

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
public import Theorems.Thm_DeciSigma1_Readers_Table_runPrefix_add
public import Theorems.Thm_DeciSigma1_Readers_StructuralReader_firstRejection_spec
public import Theorems.Thm_DeciSigma1_Automata_mem_wordsUpTo
public import Theorems.Thm_DeciSigma1_runFrom_cons
public import Theorems.Thm_DeciSigma1_runFrom_nil
public import Theorems.Thm_DeciSigma1_runFrom_snoc
attribute [local simp] DeciSigma1.Automata.mem_wordsUpTo
attribute [local simp] DeciSigma1.runFrom_cons
attribute [local simp] DeciSigma1.runFrom_nil
attribute [local simp] DeciSigma1.runFrom_snoc


section
@[expose] public section
namespace DeciSigma1.Readers
open DeciSigma1.Automata
variable {α S : Type} {k : ℕ}
namespace Table
variable (T : Table α S k)
variable {T}
end Table
open Table
section Domination
variable [DecidableEq α] [DecidableEq S]
variable {T : Table α S k} {U V W : Fin k → List α}
end Domination
namespace StructuralReader
variable (M : StructuralReader α S k)
variable {M}
private theorem take_drop_eq_of_prefix {w : List α} {a b t : ℕ} (hp : w.drop b <+: w.drop a)
    (ht : t ≤ w.length - b) : (w.drop a).take t = (w.drop b).take t := by
  obtain ⟨r, hr⟩ := hp
  rw [← hr, List.take_append_of_le_length (by simp; omega)]
end StructuralReader
end DeciSigma1.Readers
end
end

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
theorem _root_.solution {W : Fin k → List α} {i : Fin k} {a b : ℕ}
    (h : M.Eligible W i) (hab : a < b)
    (hb : b ≤ M.firstRejection W i) (hp : (W i).drop b <+: (W i).drop a) :
    M.runPrefix W i a ≠ M.runPrefix W i b := by
  intro he
  have hJ := firstRejection_spec h
  have hra : M.rejected (M.runPrefix W i (a + (M.firstRejection W i - b))) = true := by
    rw [runPrefix_add, take_drop_eq_of_prefix hp (by omega), he, ← runPrefix_add,
      show b + (M.firstRejection W i - b) = M.firstRejection W i by omega]
    exact hJ.2.1
  rw [hJ.2.2 _ (by omega)] at hra
  exact Bool.false_ne_true hra
end DeciSigma1.Readers.StructuralReader
