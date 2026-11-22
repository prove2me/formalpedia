-- Prove2me | solution 1 for DeciSigma1.Words.streamPrefix_suffix_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:00:13.358578+00:00
-- url     : https://prove2.me/submissions/9fe7f6ec-245b-4ba0-b75c-15de50bc1fad

module
public import Definitions.Def_LeanPool_DeciSigma1_Words_Periods
public import Mathlib.Tactic.Ring.RingNF
public import Mathlib.Tactic.Linarith
public import Definitions.Def_LeanPool_DeciSigma1_Words_Basic
public import Theorems.Thm_DeciSigma1_Words_drop_streamPrefix

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Words
open DeciSigma1.Words (pow)
variable {α : Type}
namespace DeciSigma1.Words
theorem _root_.solution (ξ η : ℕ → α) (m n : ℕ) :
    streamPrefix η m <:+ streamPrefix ξ n ↔ m ≤ n ∧ ∀ t < m, η t = ξ (n - m + t) := by
  constructor
  · intro h
    have hlen := h.length_le
    simp only [length_streamPrefix] at hlen
    refine ⟨hlen, fun t ht => ?_⟩
    rw [List.suffix_iff_eq_drop] at h
    simp only [length_streamPrefix] at h
    rw [drop_streamPrefix ξ (by omega)] at h
    have := congrArg (fun l => l[t]?) h
    rw [List.getElem?_eq_getElem (by simpa using ht), List.getElem?_eq_getElem (by simp; omega),
      getElem_streamPrefix _ _ _ ht, getElem_streamPrefix _ _ _ (by omega)] at this
    exact Option.some.inj this
  · rintro ⟨hle, heq⟩
    rw [List.suffix_iff_eq_drop, length_streamPrefix, length_streamPrefix,
      drop_streamPrefix ξ (by omega)]
    apply List.ext_getElem (by simp; omega)
    intro t h1 h2
    simp only [length_streamPrefix] at h1
    rw [getElem_streamPrefix _ _ _ h1, getElem_streamPrefix _ _ _ (by omega)]
    exact heq t h1
end DeciSigma1.Words
