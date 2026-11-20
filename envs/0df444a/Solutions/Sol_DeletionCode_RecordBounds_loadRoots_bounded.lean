-- Prove2me | solution 1 for DeletionCode.RecordBounds.loadRoots_bounded
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:02:46.229735+00:00
-- url     : https://prove2.me/submissions/8e57f18b-3590-4c52-8397-9137ce8d0ff2

import Definitions.Def_DeletionCode_GeneratingRecovery
import Definitions.Def_DeletionCode_RecordCodec
import Definitions.Def_DeletionCode_RecordBounds
import Theorems.Thm_DeletionCode_RecordBounds_negativeLength_pos
import Theorems.Thm_DeletionCode_RecordBounds_loadRoot_position_bound

set_option autoImplicit true
open DeletionCode DeletionCode.RecordBounds
open Windows PartialWords HeaderRecovery PathMemory ConcreteDecoder RecordCodec
variable {B : Type*} [DecidableEq B]
namespace DeletionCode.RecordBounds
theorem _root_.solution (x : Letters) (n k : ℕ) (header : B → Header)
    (hlo : ∀ b, 1 ≤ (header b).rho) (hhi : ∀ b, (header b).rho ≤ k + 1)
    (roots : List (B × ℕ)) (mem result : Bank B)
    (hs : loadRoots x n k header mem roots = some result) :
    ∀ b a, (b, a) ∈ roots → a < n := by
  induction roots generalizing mem with
  | nil => simp
  | cons root rest ih =>
    rcases root with ⟨b, a⟩
    cases hload : ConcreteFill.loadRoot x n a (negativeLength k (header b))
      (mem b) (negativeLength k (header b)) with
    | none => simp [loadRoots, hload] at hs
    | some t =>
      have hrest : loadRoots x n k header (Function.update mem b t) rest = some result := by
        simpa [loadRoots, hload] using hs
      intro c j hj
      rcases List.mem_cons.mp hj with heq | hj
      · cases heq
        exact loadRoot_position_bound x n a (negativeLength k (header b)) (mem b) t
          (negativeLength k (header b)) (negativeLength_pos k (header b) (hlo b) (hhi b)) hload
      · exact ih (Function.update mem b t) hrest c j hj
end DeletionCode.RecordBounds
