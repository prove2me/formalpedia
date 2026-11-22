-- Prove2me | solution 1 for DeciSigma1.Words.prepend_prefix
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:12:26.434218+00:00
-- url     : https://prove2.me/submissions/b4a7f257-6806-4f6a-a999-658c3db783a2

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
theorem _root_.solution (w : List α) (ξ : ℕ → α) :
    streamPrefix (prepend w ξ) w.length = w := by
  apply List.ext_getElem <;> simp [streamPrefix, prepend]
end DeciSigma1.Words
