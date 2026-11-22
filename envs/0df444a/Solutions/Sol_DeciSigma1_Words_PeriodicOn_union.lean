-- Prove2me | solution 1 for DeciSigma1.Words.PeriodicOn.union
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:38:56.310999+00:00
-- url     : https://prove2.me/submissions/1940354c-0027-49b6-8881-cffb64abd901

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
open DeciSigma1.Words.PeriodicOn
variable {w : List α} {d s e : ℕ}
namespace DeciSigma1.Words.PeriodicOn
theorem _root_.solution {s₂ e₂ : ℕ} (h₁ : PeriodicOn w d s e) (h₂ : PeriodicOn w d s₂ e₂)
    (hov : s₂ + d ≤ e) : PeriodicOn w d s (max e e₂) := by
  intro p hp hpe
  by_cases hp1 : p + d < e
  · exact h₁ p hp hp1
  · exact h₂ p (by omega) (by omega)
end DeciSigma1.Words.PeriodicOn
