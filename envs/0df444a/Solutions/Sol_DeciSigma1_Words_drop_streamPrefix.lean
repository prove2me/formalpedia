-- Prove2me | solution 1 for DeciSigma1.Words.drop_streamPrefix
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:59:36.549806+00:00
-- url     : https://prove2.me/submissions/dc5a7fde-b559-40b0-8338-436b8630bc3c

module
public import Definitions.Def_LeanPool_DeciSigma1_Words_Periods
public import Mathlib.Tactic.Ring.RingNF
public import Mathlib.Tactic.Linarith
public import Definitions.Def_LeanPool_DeciSigma1_Words_Basic
public import Theorems.Thm_DeciSigma1_Words_streamPrefix_add

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Words
open DeciSigma1.Words (pow)
variable {α : Type}
namespace DeciSigma1.Words
theorem _root_.solution (ξ : ℕ → α) {a n : ℕ} (ha : a ≤ n) :
    (streamPrefix ξ n).drop a = streamPrefix (fun t => ξ (a + t)) (n - a) := by
  conv_lhs => rw [show n = a + (n - a) by omega, streamPrefix_add]
  exact List.drop_left' (by simp)
end DeciSigma1.Words
