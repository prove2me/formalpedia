-- Prove2me | solution 1 for DeciSigma1.Words.suffixOfLength_suffix_suffixOfLength
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:07:28.581771+00:00
-- url     : https://prove2.me/submissions/990fe690-3c31-4039-b6c1-b0697236cef7

module
public import Definitions.Def_LeanPool_DeciSigma1_Readers_Basic
public import Mathlib.Order.Interval.Finset.Nat
public import Definitions.Def_LeanPool_DeciSigma1_Words_SuffixChains

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Words
open DeciSigma1.Readers
variable {α : Type}
namespace DeciSigma1.Words
theorem _root_.solution (t : List α) {b b' : ℕ} (h : b ≤ b') :
    suffixOfLength t b <:+ suffixOfLength t b' := by
  unfold suffixOfLength
  by_cases hb : b' ≤ t.length
  · have : t.drop (t.length - b) = (t.drop (t.length - b')).drop (b' - b) := by
      rw [List.drop_drop]; congr 1; omega
    rw [this]; exact List.drop_suffix _ _
  · rw [show t.length - b' = 0 by omega, List.drop_zero]; exact List.drop_suffix _ _
end DeciSigma1.Words
