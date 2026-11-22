-- Prove2me | solution 1 for DeciSigma1.Words.PeriodicFrom.add_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:39:45.803885+00:00
-- url     : https://prove2.me/submissions/6d581495-d2ae-4e15-b381-6710e94d4a58

module
public import Definitions.Def_LeanPool_DeciSigma1_Words_Periods
public import Mathlib.Tactic.Ring.RingNF
public import Mathlib.Tactic.Linarith
public import Definitions.Def_LeanPool_DeciSigma1_Words_Basic

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Words
open DeciSigma1.Words (pow)
variable {α : Type}
namespace DeciSigma1.Words
namespace PeriodicFrom
theorem _root_.solution {ξ : ℕ → α} {A p : ℕ} (h : PeriodicFrom ξ A p) (s m : ℕ) :
    ξ (A + s + m * p) = ξ (A + s) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have h1 : ξ (A + (s + m * p + p)) = ξ (A + (s + m * p)) := h (s + m * p)
    calc ξ (A + s + (m + 1) * p) = ξ (A + (s + m * p + p)) := by congr 1; ring
      _ = ξ (A + (s + m * p)) := h1
      _ = ξ (A + s + m * p) := by congr 1; ring
      _ = ξ (A + s) := ih
end PeriodicFrom
end DeciSigma1.Words
