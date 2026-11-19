-- Prove2me | solution 1 for DeletionCode.ConcreteDecoder.finish_eq_some_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:57:04.906181+00:00
-- url     : https://prove2.me/submissions/599752c1-92f1-482c-be38-4ca0c365453e

import Definitions.Def_DeletionCode_ConcreteFill
import Definitions.Def_DeletionCode_ConcreteStart
import Definitions.Def_DeletionCode_PathMemory
import Definitions.Def_DeletionCode_ConcreteDecoder

set_option autoImplicit true
open DeletionCode DeletionCode.ConcreteDecoder
open Windows PartialWords HeaderRecovery SelectedWindows
variable {B : Type*} [DecidableEq B]
namespace DeletionCode.ConcreteDecoder
theorem _root_.solution [Fintype B] (k : ℕ) (header : B → Header)
    (mem : Bank B) (output : Output k header) :
    finish k header mem = some output ↔
      ∀ b, readBits (mem b) 0 (negativeLength k (header b)) = some (output b) := by
  unfold finish
  split
  · rename_i h
    constructor
    · intro heq
      have heq' := Option.some.inj heq
      intro b
      rw [← heq']
      exact h b
    · intro hout
      congr 1
      funext b
      simp [hout b]
  · rename_i h
    constructor
    · simp
    · intro hout
      apply False.elim
      apply h
      intro b
      simp [hout b]
end DeletionCode.ConcreteDecoder
