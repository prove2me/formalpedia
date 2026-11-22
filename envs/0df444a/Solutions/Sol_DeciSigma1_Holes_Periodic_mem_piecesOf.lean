-- Prove2me | solution 1 for DeciSigma1.Holes.Periodic.mem_piecesOf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:46:16.84761+00:00
-- url     : https://prove2.me/submissions/9b2eac52-c3dd-4326-a3a4-839af3abc6ba

module
public import Definitions.Def_LeanPool_DeciSigma1_Readers_Basic
public import Definitions.Def_LeanPool_DeciSigma1_Words_Periods
public import Mathlib.Order.Nat
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Basic
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
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Periodic
open DeciSigma1.Readers DeciSigma1.Words
variable {α : Type} {k : ℕ}
variable [DecidableEq α] (W : Fin k → List α) (d : ℕ)
namespace DeciSigma1.Holes.Periodic
theorem _root_.solution {ρ : List α} {P : Piece W ρ.length} :
    P ∈ piecesOf W ρ ↔ IsConjugate P.root ρ := by
  simp [piecesOf]
end DeciSigma1.Holes.Periodic
