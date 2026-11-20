-- Prove2me | solution 1 for DeletionCode.ConcreteDecoder.run_append
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:17:22.718549+00:00
-- url     : https://prove2.me/submissions/6fa275c8-0b8b-46b1-bada-ad317ba8267d

import Definitions.Def_DeletionCode_ConcreteFill
import Definitions.Def_DeletionCode_ConcreteStart
import Definitions.Def_DeletionCode_PathMemory
import Definitions.Def_DeletionCode_ConcreteDecoder

set_option autoImplicit true
open DeletionCode DeletionCode.ConcreteDecoder
open Windows PartialWords HeaderRecovery SelectedWindows
variable {B : Type*} [DecidableEq B]
namespace DeletionCode.ConcreteDecoder
theorem _root_.solution (x : Letters) (n k : ℕ) (header : B → Header)
    (first second : List (Instruction B)) (mem : Bank B) :
    run x n k header mem (first ++ second) =
      (run x n k header mem first).bind (fun t => run x n k header t second) := by
  induction first generalizing mem with
  | nil => rfl
  | cons instruction rest ih =>
    simp only [List.cons_append, run]
    cases he : execute x n k header mem instruction with
    | none => rfl
    | some t => exact ih t
end DeletionCode.ConcreteDecoder
