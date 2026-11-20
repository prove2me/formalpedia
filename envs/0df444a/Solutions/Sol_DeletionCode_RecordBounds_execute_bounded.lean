-- Prove2me | solution 1 for DeletionCode.RecordBounds.execute_bounded
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:02:25.803618+00:00
-- url     : https://prove2.me/submissions/de71710f-84f9-4970-9b14-495ce8077b59

import Definitions.Def_DeletionCode_GeneratingRecovery
import Definitions.Def_DeletionCode_RecordCodec
import Definitions.Def_DeletionCode_RecordBounds
import Theorems.Thm_DeletionCode_RecordBounds_pathLength_le
import Theorems.Thm_DeletionCode_RecordBounds_startNegative_bounds
import Theorems.Thm_DeletionCode_RecordBounds_startPositive_bounds
import Theorems.Thm_DeletionCode_RecordBounds_fillFromBase_seed_bound
import Theorems.Thm_DeletionCode_PathMemory_readPath_bounds


set_option autoImplicit true
open DeletionCode DeletionCode.RecordBounds
open Windows PartialWords HeaderRecovery PathMemory ConcreteDecoder RecordCodec
variable {B : Type*} [DecidableEq B]
namespace DeletionCode.RecordBounds
theorem _root_.solution (x : Letters) (n k : ℕ) (header : B → Header)
    (mem result : Bank B) (instruction : Instruction B)
    (hs : execute x n k header mem instruction = some result) :
    InstructionBounded (windowLength k) instruction := by
  cases instruction with
  | start source sourceSide sourceOffset dest destSide destOffset extra =>
    cases hread : readPath k (header source) (mem source) sourceSide sourceOffset k with
    | none => simp [execute, hread] at hs
    | some bits =>
      have hsource := readPath_bounds k (header source) (mem source)
        sourceSide sourceOffset k bits hread
      have hsourceLen := pathLength_le k (header source) sourceSide
      constructor
      · omega
      · cases destSide with
        | false =>
          cases hstart : ConcreteStart.startNegative k (header dest) destOffset bits (mem dest) with
          | none => simp [execute, hread, hstart] at hs
          | some t =>
            have hd := startNegative_bounds k (header dest) destOffset bits (mem dest) t hstart
            have hlen : negativeLength k (header dest) ≤ 2 * windowLength k :=
              pathLength_le k (header dest) false
            omega
        | true =>
          cases hstart : ConcreteStart.startPositive k (header dest) destOffset bits extra (mem dest) with
          | none => simp [execute, hread, hstart] at hs
          | some t =>
            have hd := startPositive_bounds k (header dest) destOffset bits extra (mem dest) t hstart
            have hlen : positiveLength k (header dest) ≤ 2 * windowLength k :=
              pathLength_le k (header dest) true
            omega
  | fillBase dest window seedOffset =>
    cases hfill : ConcreteFill.fillFromBase x n k (windowLength k) (mem dest)
      (negativeLength k (header dest)) (SelectedWindows.windowStart (negativeExtra k (header dest)) window)
      seedOffset with
    | none => simp [execute, hfill] at hs
    | some t =>
      have hb := fillFromBase_seed_bound x n k (windowLength k) (mem dest) t
        (negativeLength k (header dest))
        (SelectedWindows.windowStart (negativeExtra k (header dest)) window) seedOffset hfill
      change seedOffset ≤ 2 * windowLength k
      omega
  | fillSupplier source sourceSide sourceOffset dest window =>
    cases hread : readPath k (header source) (mem source) sourceSide sourceOffset (windowLength k) with
    | none => simp [execute, hread] at hs
    | some bits =>
      have hb := readPath_bounds k (header source) (mem source) sourceSide sourceOffset
        (windowLength k) bits hread
      have hlen := pathLength_le k (header source) sourceSide
      change sourceOffset ≤ 2 * windowLength k
      omega
end DeletionCode.RecordBounds
