-- Prove2me | solution 1 for DeletionCode.RecordBounds.run_bounded
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:03:12.924288+00:00
-- url     : https://prove2.me/submissions/b21825f2-eb1b-49d6-9e62-1fc411c2087c

import Definitions.Def_DeletionCode_GeneratingRecovery
import Definitions.Def_DeletionCode_RecordCodec
import Definitions.Def_DeletionCode_RecordBounds
import Theorems.Thm_DeletionCode_RecordBounds_execute_bounded

set_option autoImplicit true
open DeletionCode DeletionCode.RecordBounds
open Windows PartialWords HeaderRecovery PathMemory ConcreteDecoder RecordCodec
variable {B : Type*} [DecidableEq B]
namespace DeletionCode.RecordBounds
theorem _root_.solution (x : Letters) (n k : ℕ) (header : B → Header)
    (instructions : List (Instruction B)) (mem result : Bank B)
    (hs : run x n k header mem instructions = some result) :
    ∀ instruction ∈ instructions, InstructionBounded (windowLength k) instruction := by
  induction instructions generalizing mem with
  | nil => simp
  | cons instruction rest ih =>
    cases hexec : execute x n k header mem instruction with
    | none => simp [run, hexec] at hs
    | some next =>
      have hrest : run x n k header next rest = some result := by simpa [run, hexec] using hs
      intro q hq
      rcases List.mem_cons.mp hq with rfl | hq
      · exact execute_bounded x n k header mem next _ hexec
      · exact ih next hrest q hq
end DeletionCode.RecordBounds
