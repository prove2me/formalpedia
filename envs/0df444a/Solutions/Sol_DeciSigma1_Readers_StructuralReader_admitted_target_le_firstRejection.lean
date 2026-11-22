-- Prove2me | solution 1 for DeciSigma1.Readers.StructuralReader.admitted_target_le_firstRejection
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:14:16.831786+00:00
-- url     : https://prove2.me/submissions/99240ab8-6058-4b4b-9508-8e82dceec9c2

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
public import Theorems.Thm_DeciSigma1_Readers_Table_runPrefix_succ
public import Theorems.Thm_DeciSigma1_Readers_StructuralReader_Eligible_runPrefix_ne
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
theorem _root_.solution {W : Fin k → List α} {j : Fin k} {b : ℕ} {p : S}
    (h : M.Eligible W j) (hb : b ≤ (W j).length) (hadm : M.admitted p (M.runPrefix W j b) = true) :
    b ≤ M.firstRejection W j := by
  by_contra hlt
  obtain ⟨c, rfl⟩ : ∃ c, b = c + 1 := ⟨b - 1, by omega⟩
  rw [runPrefix_succ W j (by omega)] at hadm
  have hr := rejected_of_firstRejection_le h (by omega) (by omega : c ≤ (W j).length)
  have hne : M.step (M.runPrefix W j c) ((W j)[c]'(by omega)) ≠ M.dead := by
    rw [← runPrefix_succ W j (by omega)]; exact h.runPrefix_ne _
  rw [M.not_admitted_step_of_rejected p _ _ hr hne] at hadm
  exact Bool.false_ne_true hadm
end DeciSigma1.Readers.StructuralReader
