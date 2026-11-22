-- Prove2me | solution 1 for DeciSigma1.Words.Ray.suffixBeforeOnset_suffix_prefixBeforeOnset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:12:52.658728+00:00
-- url     : https://prove2.me/submissions/90a56951-5d04-4afa-9739-a7b5ce718616

module
public import Definitions.Def_LeanPool_DeciSigma1_Words_Periods
public import Mathlib.Tactic.Ring.RingNF
public import Mathlib.Tactic.Linarith
public import Definitions.Def_LeanPool_DeciSigma1_Words_Basic
public import Theorems.Thm_DeciSigma1_Words_streamPrefix_suffix_iff

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
namespace DeciSigma1.Words.Ray
theorem _root_.solution (Ω : Ray α) (J : ℕ) :
    Ω.suffixBeforeOnset J <:+ Ω.prefixBeforeOnset := by
  rw [suffixBeforeOnset, prefixBeforeOnset, streamPrefix_suffix_iff]
  exact ⟨by omega, fun t ht => by congr 1; omega⟩
end DeciSigma1.Words.Ray
