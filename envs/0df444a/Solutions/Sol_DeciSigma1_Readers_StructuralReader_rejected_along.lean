-- Prove2me | solution 1 for DeciSigma1.Readers.StructuralReader.rejected_along
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:11:50.177548+00:00
-- url     : https://prove2.me/submissions/c50b1cfb-6b78-48ea-bb0f-4bde80e88b18

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
open Table
open DeciSigma1.Readers.StructuralReader
variable (M : StructuralReader α S k)
variable {M}
namespace DeciSigma1.Readers.StructuralReader
theorem _root_.solution {q : S} {u : List α} (hq : M.rejected q = true) (hl : M.LiveAlong q u) :
    ∀ a ≤ u.length, M.rejected (runFrom M.step q (u.take a)) = true := by
  intro a ha
  induction a with
  | zero => simpa using hq
  | succ a ih =>
    have hlt : a < u.length := by omega
    rw [List.take_add_one, List.getElem?_eq_getElem hlt, Option.toList_some,
      runFrom_snoc]
    apply M.rejected_step _ _ (ih (by omega))
    have := hl (a + 1) ha
    rwa [List.take_add_one, List.getElem?_eq_getElem hlt, Option.toList_some,
      runFrom_snoc] at this
end DeciSigma1.Readers.StructuralReader
