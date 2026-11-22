-- Prove2me | solution 1 for DeciSigma1.Words.eq_of_retainedCount_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:44:40.445805+00:00
-- url     : https://prove2.me/submissions/bc4d6d76-33f3-44a7-9f10-a0b3fc572bfd

module
public import Definitions.Def_LeanPool_DeciSigma1_Readers_Basic
public import Mathlib.Tactic.Ring.RingNF
public import Mathlib.Order.Interval.Finset.Nat
public import Definitions.Def_LeanPool_DeciSigma1_Words_Deletion
public import Theorems.Thm_DeciSigma1_Words_retainedCount_mono
public import Theorems.Thm_DeciSigma1_Words_retainedCount_lt_of_not_mem

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Words
open DeciSigma1.Readers
variable {α S : Type} {k : ℕ}
variable {D : Finset ℕ}
namespace DeciSigma1.Words
theorem _root_.solution {p q : ℕ} (h : retainedCount D p = retainedCount D q)
    (hp : p = 0 ∨ p - 1 ∉ D) (hq : q = 0 ∨ q - 1 ∉ D) : p = q := by
  rcases lt_trichotomy p q with hlt | heq | hlt
  · have := retainedCount_lt_of_not_mem (hq.resolve_left (by omega)) (show q - 1 < q by omega)
    have := retainedCount_mono (D := D) (show p ≤ q - 1 by omega)
    omega
  · exact heq
  · have := retainedCount_lt_of_not_mem (hp.resolve_left (by omega)) (show p - 1 < p by omega)
    have := retainedCount_mono (D := D) (show q ≤ p - 1 by omega)
    omega
end DeciSigma1.Words
