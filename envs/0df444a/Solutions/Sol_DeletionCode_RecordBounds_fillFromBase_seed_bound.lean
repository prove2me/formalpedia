-- Prove2me | solution 1 for DeletionCode.RecordBounds.fillFromBase_seed_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:01:28.810178+00:00
-- url     : https://prove2.me/submissions/701e0d8e-e083-4832-a246-46c25a405cf2

import Definitions.Def_DeletionCode_GeneratingRecovery
import Definitions.Def_DeletionCode_RecordCodec
import Definitions.Def_DeletionCode_RecordBounds
import Theorems.Thm_DeletionCode_SeedLookup_recoverWindow_sound


set_option autoImplicit true
open DeletionCode DeletionCode.RecordBounds
open Windows PartialWords HeaderRecovery PathMemory ConcreteDecoder RecordCodec
namespace DeletionCode.RecordBounds
theorem _root_.solution (x : Letters) (n k L : ℕ) (s t : Memory)
    (m start r : ℕ) (h : ConcreteFill.fillFromBase x n k L s m start r = some t) :
    r + k ≤ L := by
  cases hseed : readBits s (start + r) k with
  | none => simp [ConcreteFill.fillFromBase, hseed] at h
  | some seed =>
    cases hwindow : SeedLookup.recoverWindow x n k L r seed with
    | none => simp [ConcreteFill.fillFromBase, hseed, hwindow] at h
    | some bits =>
      obtain ⟨a, ha, _⟩ := SeedLookup.recoverWindow_sound x n k L r seed bits hwindow
      exact ha.1
end DeletionCode.RecordBounds
