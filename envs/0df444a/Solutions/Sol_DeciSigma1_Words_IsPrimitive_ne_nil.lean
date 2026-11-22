-- Prove2me | solution 1 for DeciSigma1.Words.IsPrimitive.ne_nil
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:38:07.705777+00:00
-- url     : https://prove2.me/submissions/6ddca914-e75e-4c81-a462-4bd18e3f89f6

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
namespace DeciSigma1.Words
namespace IsPrimitive
theorem _root_.solution {ρ : List α} (h : IsPrimitive ρ) : ρ ≠ [] := h.1
end IsPrimitive
end DeciSigma1.Words
