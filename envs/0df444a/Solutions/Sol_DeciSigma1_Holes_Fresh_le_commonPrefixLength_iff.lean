-- Prove2me | solution 1 for DeciSigma1.Holes.Fresh.le_commonPrefixLength_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:45:16.976988+00:00
-- url     : https://prove2.me/submissions/019116cf-ba64-424a-ba61-f45c4c7930f4

module
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Hierarchy
public import Mathlib.Order.Nat
public import Mathlib.Algebra.GroupWithZero.Nat
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Parsing
public import Theorems.Thm_DeciSigma1_Automata_mem_wordsUpTo
public import Theorems.Thm_DeciSigma1_Holes_Fresh_marker_zero
public import Theorems.Thm_DeciSigma1_Holes_Fresh_mem_active_one
public import Theorems.Thm_DeciSigma1_Holes_Fresh_mem_active_zero
public import Theorems.Thm_DeciSigma1_runFrom_cons
public import Theorems.Thm_DeciSigma1_runFrom_nil
public import Theorems.Thm_DeciSigma1_runFrom_snoc
attribute [local simp] DeciSigma1.Automata.mem_wordsUpTo
attribute [local simp] DeciSigma1.Holes.Fresh.marker_zero
attribute [local simp] DeciSigma1.Holes.Fresh.mem_active_one
attribute [local simp] DeciSigma1.Holes.Fresh.mem_active_zero
attribute [local simp] DeciSigma1.runFrom_cons
attribute [local simp] DeciSigma1.runFrom_nil
attribute [local simp] DeciSigma1.runFrom_snoc



set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Fresh
open Finset
variable {β : Type} [DecidableEq β]
namespace DeciSigma1.Holes.Fresh
theorem _root_.solution {A B : List β} {d : ℕ} :
    d ≤ commonPrefixLength A B ↔ d ≤ A.length ∧ d ≤ B.length ∧ A.take d = B.take d := by
  induction A generalizing B d with
  | nil => cases d <;> simp [commonPrefixLength]
  | cons a A ih =>
    cases B with
    | nil => cases d <;> simp [commonPrefixLength]
    | cons b B =>
      cases d with
      | zero => simp
      | succ d =>
        simp only [commonPrefixLength]
        split_ifs with hab
        · subst hab
          simp only [List.length_cons, List.take_succ_cons, List.cons.injEq, true_and,
            Nat.add_le_add_iff_right]
          exact ih
        · simp [hab]
end DeciSigma1.Holes.Fresh
