-- Prove2me | solution 1 for DeciSigma1.Words.IsConjugate.symm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:34:09.289195+00:00
-- url     : https://prove2.me/submissions/a3c0e673-ee1d-4456-aeaf-9222ffc66f8c

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
theorem _root_.solution (h : IsConjugate ρ ρ') : IsConjugate ρ' ρ :=
  isConjugate_iff_isRotated.mpr (isConjugate_iff_isRotated.mp h).symm
end DeciSigma1.Words.IsConjugate
