-- Prove2me | solution 1 for DeciSigma1.Words.two_le_card_of_eligible
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:49:36.668516+00:00
-- url     : https://prove2.me/submissions/bd832c1c-a128-4b96-81fc-b4488805da06

module
public import Definitions.Def_LeanPool_DeciSigma1_Readers_Basic
public import Mathlib.Order.Interval.Finset.Nat
public import Definitions.Def_LeanPool_DeciSigma1_Words_SuffixChains

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Words
open DeciSigma1.Readers
variable {α : Type}
variable [DecidableEq α]
variable {S : Type} [Fintype S] {k : ℕ} (M : StructuralReader α S k)
  {W : Fin k → List α} {j : Fin k}
omit [DecidableEq α]
namespace DeciSigma1.Words
theorem _root_.solution (h : M.Eligible W j) : 2 ≤ Fintype.card S := by
  classical
  have hne : M.endState W j ≠ M.dead := by
    intro he; have := h.2; rw [he, M.rejected_dead] at this; exact Bool.false_ne_true this
  have := Finset.card_le_univ ({M.endState W j, M.dead} : Finset S)
  rw [Finset.card_pair hne] at this
  exact this
end DeciSigma1.Words
