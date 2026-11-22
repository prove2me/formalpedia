-- Prove2me | solution 1 for DeciSigma1.Words.IsConjugate.trans
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:33:51.602803+00:00
-- url     : https://prove2.me/submissions/8918257e-87e8-41e9-b01b-9bb2f4ef59c7

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
theorem _root_.solution (h₁ : IsConjugate ρ ρ') (h₂ : IsConjugate ρ' ρ'') : IsConjugate ρ ρ'' :=
  isConjugate_iff_isRotated.mpr ((isConjugate_iff_isRotated.mp h₁).trans
    (isConjugate_iff_isRotated.mp h₂))
end DeciSigma1.Words.IsConjugate
