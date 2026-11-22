-- Prove2me | solution 1 for DeciSigma1.Words.prepend_prefix_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:13:02.814245+00:00
-- url     : https://prove2.me/submissions/9cbbc773-184b-4070-ad0d-43354be4bc39

module
public import Definitions.Def_LeanPool_DeciSigma1_Words_Periods
public import Mathlib.Tactic.Ring.RingNF
public import Mathlib.Tactic.Linarith
public import Definitions.Def_LeanPool_DeciSigma1_Words_Basic
public import Theorems.Thm_DeciSigma1_Words_streamPrefix_succ
public import Theorems.Thm_DeciSigma1_Words_prepend_prefix

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Words
open DeciSigma1.Words (pow)
variable {α : Type*}
namespace DeciSigma1.Words
theorem _root_.solution (w : List α) (ξ : ℕ → α) (n : ℕ) :
    streamPrefix (prepend w ξ) (w.length + n) = w ++ streamPrefix ξ n := by
  induction n with
  | zero => simpa only [Nat.add_zero, show streamPrefix ξ 0 = [] from rfl,
      List.append_nil] using prepend_prefix w ξ
  | succ n ih =>
    rw [← Nat.add_assoc, streamPrefix_succ, ih]
    simp [prepend, List.append_assoc, streamPrefix_succ]
end DeciSigma1.Words
