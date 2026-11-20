-- Prove2me | solution 1 for DeletionCode.RecordBounds.decode_bounded
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:03:47.493061+00:00
-- url     : https://prove2.me/submissions/74d9abcd-fde7-4a55-9471-2fe0a5406493

import Definitions.Def_DeletionCode_GeneratingRecovery
import Definitions.Def_DeletionCode_RecordCodec
import Definitions.Def_DeletionCode_RecordBounds
import Theorems.Thm_DeletionCode_RecordBounds_run_bounded
import Theorems.Thm_DeletionCode_RecordBounds_loadRoots_bounded

set_option autoImplicit true
open DeletionCode DeletionCode.RecordBounds
open Windows PartialWords HeaderRecovery PathMemory ConcreteDecoder RecordCodec
variable {B : Type*} [DecidableEq B]
namespace DeletionCode.RecordBounds
theorem _root_.solution [Fintype B] (x : Letters) (n k : ℕ) (header : B → Header)
    (hlo : ∀ b, 1 ≤ (header b).rho) (hhi : ∀ b, (header b).rho ≤ k + 1)
    (roots : List (B × ℕ)) (instructions : List (Instruction B)) (output : Output k header)
    (hs : decode x n k header roots instructions = some output) :
    (∀ b a, (b, a) ∈ roots → a < n) ∧
      ∀ instruction ∈ instructions, InstructionBounded (windowLength k) instruction := by
  cases hload : loadRoots x n k header (fun _ => empty) roots with
  | none => simp [decode, hload] at hs
  | some initial =>
    cases hrun : run x n k header initial instructions with
    | none => simp [decode, hload, hrun] at hs
    | some result =>
      exact ⟨loadRoots_bounded x n k header hlo hhi roots _ initial hload,
        run_bounded x n k header instructions initial result hrun⟩
end DeletionCode.RecordBounds
