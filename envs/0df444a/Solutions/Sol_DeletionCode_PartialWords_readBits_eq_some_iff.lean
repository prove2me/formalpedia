-- Prove2me | solution 1 for DeletionCode.PartialWords.readBits_eq_some_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:00:48.273207+00:00
-- url     : https://prove2.me/submissions/3bd6343e-dcb7-4961-a008-15c2c14b55a5

import Definitions.Def_DeletionCode_Windows
import Mathlib.Data.Fintype.Basic
import Definitions.Def_DeletionCode_PartialWords

set_option autoImplicit true
open DeletionCode DeletionCode.PartialWords
open Windows
namespace DeletionCode.PartialWords
theorem _root_.solution (s : Memory) (start len : ℕ) (bits : Bits len) :
    readBits s start len = some bits ↔
      ∀ i, s (start + i.val) = some (bits i) := by
  unfold readBits
  split
  · rename_i h
    constructor
    · intro heq
      have heq' := Option.some.inj heq
      intro i
      rw [← heq']
      exact h i
    · intro hb
      congr 1
      funext i
      simp [hb i]
  · rename_i h
    constructor
    · simp
    · intro hb
      apply False.elim
      apply h
      intro i
      simp [hb i]
end DeletionCode.PartialWords
