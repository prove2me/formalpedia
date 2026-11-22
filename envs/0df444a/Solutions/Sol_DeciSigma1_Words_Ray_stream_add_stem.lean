-- Prove2me | solution 1 for DeciSigma1.Words.Ray.stream_add_stem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:12:44.996023+00:00
-- url     : https://prove2.me/submissions/968c9921-4013-40c0-a9ff-cb39e1f76d66

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
open DeciSigma1.Words.Ray
variable (Ω : Ray α)
variable {Ω}
namespace DeciSigma1.Words.Ray
theorem _root_.solution (t : ℕ) : Ω.stream (Ω.stem.length + t) = Ω.periodicTail t := by
  rw [stream_of_ge (Nat.le_add_right _ _), Nat.add_sub_cancel_left]
end DeciSigma1.Words.Ray
