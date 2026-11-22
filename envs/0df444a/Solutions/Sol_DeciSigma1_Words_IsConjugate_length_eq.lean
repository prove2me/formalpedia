-- Prove2me | solution 1 for DeciSigma1.Words.IsConjugate.length_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:57:43.424845+00:00
-- url     : https://prove2.me/submissions/f6dfce15-5693-4b88-a23b-ca4ee4e61c12

module
public import Mathlib.Data.List.PeriodicityLemma
public import Mathlib.Data.Nat.ModEq
public import Mathlib.Tactic.Ring.RingNF
public import Mathlib.Tactic.Linarith
public import Definitions.Def_LeanPool_DeciSigma1_Words_Periods

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Words
variable {α : Type*}
open DeciSigma1.Words.IsConjugate
variable {ρ ρ' ρ'' : List α}
namespace DeciSigma1.Words.IsConjugate
theorem _root_.solution (h : IsConjugate ρ ρ') : ρ'.length = ρ.length := by
  obtain ⟨r, rfl⟩ := h; simp
end DeciSigma1.Words.IsConjugate
