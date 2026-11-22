-- Prove2me | solution 1 for DeciSigma1.Words.PeriodicOn.eq_of_le_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:38:05.972245+00:00
-- url     : https://prove2.me/submissions/d21bab0d-2c9d-45cd-a34f-8b371b4e75ca

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
theorem _root_.solution (h : PeriodicOn w d s e) {p : ℕ} (hp : s ≤ p) :
    ∀ j, p + j * d < e → w[p]? = w[p + j * d]? := by
  intro j
  induction j with
  | zero => intro; simp
  | succ j ih =>
    intro hj
    rw [ih (by nlinarith), h (p + j * d) (by omega) (by nlinarith)]
    congr 1
    ring
end DeciSigma1.Words.PeriodicOn
