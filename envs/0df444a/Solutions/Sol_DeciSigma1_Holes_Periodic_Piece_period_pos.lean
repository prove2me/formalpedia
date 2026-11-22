-- Prove2me | solution 1 for DeciSigma1.Holes.Periodic.Piece.period_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:44:29.282813+00:00
-- url     : https://prove2.me/submissions/a812cf73-aae1-49e3-aec9-c7b5e8aa1853

module
public import Definitions.Def_LeanPool_DeciSigma1_Readers_Basic
public import Definitions.Def_LeanPool_DeciSigma1_Words_Periods
public import Mathlib.Order.Nat
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Basic
public import Theorems.Thm_DeciSigma1_Automata_mem_wordsUpTo
public import Theorems.Thm_DeciSigma1_Words_IsPrimitive_ne_nil
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
open DeciSigma1.Holes.Periodic.Piece
variable {W : Fin k → List α} {d : ℕ}
namespace DeciSigma1.Holes.Periodic.Piece
theorem _root_.solution (P : Piece W d) : 0 < d := by
  rcases Nat.eq_zero_or_pos d with h | h
  · exact absurd (by simp [h]) P.primitive.ne_nil
  · exact h
end DeciSigma1.Holes.Periodic.Piece
