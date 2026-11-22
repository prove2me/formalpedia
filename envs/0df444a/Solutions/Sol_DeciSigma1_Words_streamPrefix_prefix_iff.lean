-- Prove2me | solution 1 for DeciSigma1.Words.streamPrefix_prefix_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:12:44.519583+00:00
-- url     : https://prove2.me/submissions/98e3e2ec-ef87-4ebc-8e1f-edf6fb415603

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
theorem _root_.solution (ξ η : ℕ → α) (m m' : ℕ) :
    streamPrefix η m <+: streamPrefix ξ m' ↔ m ≤ m' ∧ ∀ t < m, η t = ξ t := by
  constructor
  · intro h
    have hlen := h.length_le
    simp only [length_streamPrefix] at hlen
    refine ⟨hlen, fun t ht => ?_⟩
    have := h.getElem (by simpa using ht)
    simpa [streamPrefix] using this
  · rintro ⟨hle, heq⟩
    rw [List.prefix_iff_eq_take, length_streamPrefix, take_streamPrefix, min_eq_left hle]
    apply List.ext_getElem (by simp)
    intro t ht _
    simp only [streamPrefix, List.getElem_ofFn]
    exact heq t (by simpa using ht)
end DeciSigma1.Words
