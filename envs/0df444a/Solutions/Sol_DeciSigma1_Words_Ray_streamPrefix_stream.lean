-- Prove2me | solution 1 for DeciSigma1.Words.Ray.streamPrefix_stream
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:13:41.179802+00:00
-- url     : https://prove2.me/submissions/52839aaa-5b67-45a8-b99e-9ddc0908f944

module
public import Definitions.Def_LeanPool_DeciSigma1_Words_Periods
public import Mathlib.Tactic.Ring.RingNF
public import Mathlib.Tactic.Linarith
public import Definitions.Def_LeanPool_DeciSigma1_Words_Basic
public import Theorems.Thm_DeciSigma1_Words_prepend_prefix_add
public import Theorems.Thm_DeciSigma1_Words_Ray_streamPrefix_periodicTail

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Words
open DeciSigma1.Words (pow)
variable {α : Type}
open DeciSigma1.Words.Ray
variable (Ω : Ray α)
variable {Ω}
variable [DecidableEq α]
omit [DecidableEq α]
namespace DeciSigma1.Words.Ray
theorem _root_.solution (L : ℕ) :
    streamPrefix Ω.stream (Ω.stem.length + L) = Ω.stem ++ (pow Ω.loop (L + 1)).take L := by
  rw [stream, prepend_prefix_add, streamPrefix_periodicTail]
end DeciSigma1.Words.Ray
