-- Prove2me | solution 1 for DeciSigma1.Words.streamPrefix_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:58:29.934499+00:00
-- url     : https://prove2.me/submissions/4a10f80d-adb7-46b9-970b-c4b2030cff33

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
variable {α : Type*}
namespace DeciSigma1.Words
theorem _root_.solution (ξ : ℕ → α) (n : ℕ) :
    streamPrefix ξ (n + 1) = streamPrefix ξ n ++ [ξ n] := by
  simpa [streamPrefix, List.concat_eq_append] using
    (List.ofFn_succ' (fun i : Fin (n + 1) => ξ i))
end DeciSigma1.Words
