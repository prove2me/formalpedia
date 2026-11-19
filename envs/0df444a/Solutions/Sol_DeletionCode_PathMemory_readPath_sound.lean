-- Prove2me | solution 1 for DeletionCode.PathMemory.readPath_sound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:56:46.518359+00:00
-- url     : https://prove2.me/submissions/02ed9a3e-92f5-4c61-b337-aefecd9527c2

import Definitions.Def_DeletionCode_HeaderRecovery
import Definitions.Def_DeletionCode_PartialWords
import Definitions.Def_DeletionCode_SelectedWindows
import Definitions.Def_DeletionCode_PathMemory
import Theorems.Thm_DeletionCode_HeaderRecovery_rebuildPositiveFinite_correct
import Theorems.Thm_DeletionCode_PartialWords_readBits_sound


set_option autoImplicit true
open DeletionCode DeletionCode.PathMemory
open Windows HeaderRecovery PartialWords SelectedWindows
namespace DeletionCode.PathMemory
theorem _root_.solution (k : ℕ) (h : Header) (long : Letters) (s : Memory)
    (side : Bool) (start len : ℕ) (bits : PartialWords.Bits len)
    (hrho0 : 1 ≤ h.rho) (hrho1 : h.rho ≤ k + 1)
    (hbit : long (editOffset k) = h.bit)
    (hs : Sound s (negativePath k h long) (negativeLength k h))
    (hread : readPath k h s side start len = some bits) :
    Matches bits (pathLetters k h long side) start := by
  cases side with
  | false =>
    simp only [readPath] at hread
    split at hread
    · rename_i hbound
      exact readBits_sound s (negativePath k h long) (negativeLength k h)
        start len hs hbound bits hread
    · contradiction
  | true =>
    simp only [readPath] at hread
    split at hread
    · rename_i hbound
      cases hnegative : readBits s 0 (negativeLength k h) with
      | none => simp [hnegative] at hread
      | some negative =>
        have hmatch := readBits_sound s (negativePath k h long) (negativeLength k h)
          0 (negativeLength k h) hs (by omega) negative hnegative
        have hknown : ∀ i : Fin (negativeLength k h),
            negative i = negativePath k h long i.val := by
          intro i
          simpa only [Nat.zero_add] using hmatch i
        have hpositive := rebuildPositiveFinite_correct k h long negative
          hrho0 hrho1 hbit hknown
        simp only [hnegative, Option.map_some] at hread
        have heq := Option.some.inj hread
        intro i
        rw [← heq]
        exact hpositive ⟨start + i.val, by have := i.isLt; omega⟩
    · contradiction
end DeletionCode.PathMemory
