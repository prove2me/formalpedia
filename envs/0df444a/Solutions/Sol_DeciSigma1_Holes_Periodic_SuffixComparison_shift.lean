-- Prove2me | solution 1 for DeciSigma1.Holes.Periodic.SuffixComparison.shift
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:45:52.217714+00:00
-- url     : https://prove2.me/submissions/0115ca9a-d877-4e59-99cb-308585d4ebd2

module
public import Mathlib.Tactic.Positivity.Basic
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Pieces
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Transport

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Periodic
open DeciSigma1.Readers DeciSigma1.Words
open DeciSigma1.Readers.Table
variable {α : Type} {k : ℕ}
open DeciSigma1.Holes.Periodic.SuffixComparison
variable {y z : List α} {b a : ℕ}
namespace DeciSigma1.Holes.Periodic.SuffixComparison
theorem _root_.solution (h : SuffixComparison y b z a) (m : ℕ) : SuffixComparison y (b + m) z (a + m) := by
  intro n hn
  have := h (m + n) (by omega)
  rwa [← Nat.add_assoc, ← Nat.add_assoc] at this
end DeciSigma1.Holes.Periodic.SuffixComparison
