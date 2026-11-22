-- Prove2me | solution 1 for DeciSigma1.Words.streamPrefix_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:58:57.768845+00:00
-- url     : https://prove2.me/submissions/37486da5-1f6a-40cf-9c9e-27caf648a1b8

module
public import Definitions.Def_LeanPool_DeciSigma1_Words_Periods
public import Mathlib.Tactic.Ring.RingNF
public import Mathlib.Tactic.Linarith
public import Definitions.Def_LeanPool_DeciSigma1_Words_Basic
public import Theorems.Thm_DeciSigma1_Words_streamPrefix_succ

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Words
open DeciSigma1.Words (pow)
variable {α : Type*}
namespace DeciSigma1.Words
theorem _root_.solution (ξ : ℕ → α) (k n : ℕ) :
    streamPrefix ξ (k + n) = streamPrefix ξ k ++ streamPrefix (fun i => ξ (k + i)) n := by
  induction n with
  | zero => simp [streamPrefix]
  | succ n ih =>
    rw [← Nat.add_assoc, streamPrefix_succ, ih, streamPrefix_succ, List.append_assoc]
end DeciSigma1.Words
