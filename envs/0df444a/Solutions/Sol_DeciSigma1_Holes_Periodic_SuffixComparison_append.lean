-- Prove2me | solution 1 for DeciSigma1.Holes.Periodic.SuffixComparison.append
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:48:46.148286+00:00
-- url     : https://prove2.me/submissions/b5d4f9b7-2129-4b69-80d9-8e7210f05cbf

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
theorem _root_.solution {r : ℕ} (h₁ : ∀ n < r, y[b + n]? = z[a + n]?)
    (h₂ : SuffixComparison y (b + r) z (a + r)) :
    SuffixComparison y b z a := by
  intro n hn
  rcases Nat.lt_or_ge n r with h | h
  · exact h₁ n h
  · have := h₂ (n - r) (by omega)
    rwa [Nat.add_assoc, Nat.add_sub_cancel' h, Nat.add_assoc, Nat.add_sub_cancel' h] at this
end DeciSigma1.Holes.Periodic.SuffixComparison
