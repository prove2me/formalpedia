-- Prove2me | solution 1 for DeciSigma1.Holes.Tail.suffixLengthEnvelope_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:52:08.980074+00:00
-- url     : https://prove2.me/submissions/6f31b502-d306-4c04-9646-01fdbb04df42

module
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_Rays
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_ClosedFactors
public import Theorems.Thm_DeciSigma1_Holes_Tail_suffixLengthEnvelope_cons
public import Theorems.Thm_DeciSigma1_Holes_Tail_suffixLengthBound_mono

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Tail
open DeciSigma1.Words
variable {α S : Type} {k : ℕ}
namespace DeciSigma1.Holes.Tail
theorem _root_.solution (m N : ℕ) : ∀ Ss : List ℕ, Monotone (suffixLengthEnvelope m N Ss)
  | [] => fun b b' h => h
  | S :: Ss => fun b b' h => by
    have hg := suffixLengthBound_mono m N Ss
    have hG : Monotone (fun b => b + suffixLengthBound m N Ss b) :=
        fun a a' h => Nat.add_le_add h (hg h)
    have h1 := hG.iterate S h
    rw [suffixLengthEnvelope_cons, suffixLengthEnvelope_cons]
    exact solution m N Ss (Nat.add_le_add h1 (hg h1))
end DeciSigma1.Holes.Tail
