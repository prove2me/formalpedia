-- Prove2me | solution 1 for DeciSigma1.Words.pow_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:41:11.43766+00:00
-- url     : https://prove2.me/submissions/0d6f36b5-a22f-4b8f-9253-d4dafbe50820

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
variable {μ π u w : List α} {p q n : ℕ}
namespace DeciSigma1.Words
theorem _root_.solution (μ : List α) (m n : ℕ) : pow μ (m + n) = pow μ m ++ pow μ n := by
  induction m with
  | zero => simp
  | succ m ih => simpa [Nat.succ_add, List.append_assoc] using congrArg (μ ++ ·) ih
end DeciSigma1.Words
