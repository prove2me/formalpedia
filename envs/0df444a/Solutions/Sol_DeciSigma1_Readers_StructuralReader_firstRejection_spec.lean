-- Prove2me | solution 1 for DeciSigma1.Readers.StructuralReader.firstRejection_spec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:43:40.490499+00:00
-- url     : https://prove2.me/submissions/7aa696a9-d01e-4532-8621-c2cdec8f41a0

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
theorem _root_.solution {W : Fin k → List α} {i : Fin k} (h : M.Eligible W i) :
    M.firstRejection W i ≤ (W i).length ∧ M.rejected (M.runPrefix W i (M.firstRejection W i)) =
        true ∧
      ∀ a < M.firstRejection W i, M.rejected (M.runPrefix W i a) = false := by
  unfold firstRejection
  cases hf : (List.range ((W i).length + 1)).find? (fun a => M.rejected (M.runPrefix W i a)) with
  | none =>
    rw [List.find?_eq_none] at hf
    exact absurd h.2 (by simpa [endState] using hf (W i).length (by simp))
  | some j =>
    rw [List.find?_range_eq_some] at hf
    obtain ⟨h1, h2, h3⟩ := hf
    simp only [List.mem_range] at h2
    refine ⟨by simp; omega, by simpa using h1, fun a ha => ?_⟩
    simpa using h3 a ha
end DeciSigma1.Readers.StructuralReader
