-- Prove2me | solution 1 for DeciSigma1.Words.IsConjugate.isPrimitive
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:38:08.17131+00:00
-- url     : https://prove2.me/submissions/ac7d5b27-c2df-4a52-950c-85be38762879

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
theorem _root_.solution (h : IsConjugate ρ ρ') (hρ : IsPrimitive ρ) : IsPrimitive ρ' := by
  obtain ⟨r, rfl⟩ := h; exact hρ.rotate r
end DeciSigma1.Words.IsConjugate
