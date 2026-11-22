-- Prove2me | solution 1 for DeciSigma1.Words.IsConjugate.refl
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:12:25.901308+00:00
-- url     : https://prove2.me/submissions/acba29b7-e485-4f7b-b213-8b460eb7afd5

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
theorem _root_.solution (ρ : List α) : IsConjugate ρ ρ := ⟨0, by simp⟩
end DeciSigma1.Words.IsConjugate
