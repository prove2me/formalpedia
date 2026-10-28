-- Prove2me | solution 1 for CountingMatroid.Analysis.BoundedRunOtherSteps.finalization_otherSteps_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T15:47:04.612343+00:00
-- url     : https://prove2.me/submissions/917d93ff-1244-4c11-bb6a-89176508cf64

import Definitions.Def_CountingMatroidSupport_Computation_Charged
import Definitions.Def_CountingMatroidSupport_Computation_Charged_Extension1
import Definitions.Def_CountingMatroidSupport_Computation_Charged_Extension2
import Definitions.Def_CountingMatroidSupport_Computation_Cost
import Definitions.Def_CountingMatroidSupport_Computation_Cost_Extension1
import Definitions.Def_CountingMatroidSupport_Computation_Dict
import Definitions.Def_CountingMatroidSupport_Computation_Heap
import Definitions.Def_CountingMatroidSupport_Computation_Machine
import Definitions.Def_CountingMatroidSupport_Computation_Machine_Extension1
import Definitions.Def_CountingMatroidSupport_Computation_Num
import Definitions.Def_CountingMatroidSupport_Computation_Queue
import Definitions.Def_CountingMatroidSupport_Computation_Rand
import Definitions.Def_CountingMatroidSupport_Computation_Roster
import Definitions.Def_CountingMatroidSupport_Computation_Slot
import Definitions.Def_CountingMatroidSupport_Computation_Space
import Definitions.Def_CountingMatroidSupport_Computation_Std
import Definitions.Def_CountingMatroid_Analysis_BoundedRunPhase
import Definitions.Def_CountingMatroid_Analysis_BoundedRunPhaseWork
import Definitions.Def_CountingMatroid_Analysis_EstimateMedianResource
import Definitions.Def_CountingMatroid_Analysis_FinishPhaseWork
import Definitions.Def_CountingMatroid_Analysis_ObservePhaseWork
import Definitions.Def_CountingMatroid_Analysis_PhaseChainWork
import Definitions.Def_CountingMatroid_Analysis_PhaseResourcePrimitives
import Definitions.Def_CountingMatroid_Analysis_RationalHeight
import Definitions.Def_CountingMatroid_Analysis_ScheduleOpeningCost
import Definitions.Def_CountingMatroid_Analysis_ScheduleThermalSetupCost
import Definitions.Def_CountingMatroid_Model_Operations
import Definitions.Def_CountingMatroid_Model_Prelude
import Definitions.Def_CountingMatroid_Model_Program
import Definitions.Def_CountingMatroid_Model_Run
import Definitions.Def_CountingMatroid_Model_Subroutines
import Lean
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Combinatorics.Matroid.Rank.ENat
import Mathlib.Data.BitVec
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Sort
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Ring.RingNF
import Theorems.Thm_CountingMatroid_Analysis_ScheduleOtherStepsEnvelope_log2_mul_le
import Theorems.Thm_CountingMatroid_Analysis_ScheduleOtherStepsEnvelope_natPower_otherSteps_eq

namespace CountingMatroid.Analysis.ScheduleOtherStepsEnvelope
end CountingMatroid.Analysis.ScheduleOtherStepsEnvelope
namespace CountingMatroid.Analysis.LeastHalvingsCost
end CountingMatroid.Analysis.LeastHalvingsCost
namespace CountingMatroid.Analysis
end CountingMatroid.Analysis
namespace CountingMatroid.Meta
end CountingMatroid.Meta
namespace Arlib
end Arlib
namespace CountingMatroid.Analysis.BoundedRunOtherSteps
end CountingMatroid.Analysis.BoundedRunOtherSteps
namespace CountingMatroid.Analysis.RestartPhaseWork
end CountingMatroid.Analysis.RestartPhaseWork
namespace CountingMatroid.Analysis.BoundedRunPhase
end CountingMatroid.Analysis.BoundedRunPhase
namespace CountingMatroid.Analysis.FinishPhaseWeightsSize
end CountingMatroid.Analysis.FinishPhaseWeightsSize
section


set_option autoImplicit false

namespace CountingMatroid.Analysis.ScheduleOtherStepsEnvelope

open CountingMatroid.Model
open CountingMatroid.Model.Subroutines



















/-- INTERNAL: A charged rational binary operation is bounded by its input encodings. -/
theorem rationalBinary_otherSteps_le (instr : Arlib.Computation.Op)
    (a b result : ℚ) :
    otherSteps (Arlib.Computation.Charged.opMany
      (CountingMatroid.Model.Operations.Op.word instr)
      ((a.num.natAbs.log2 + a.den.log2 + 3 +
        (b.num.natAbs.log2 + b.den.log2 + 3)) ^ 2) result) ≤
      (binaryRatLength a + binaryRatLength b) ^ 2 := by
  have hcost (z : ℕ) : otherSteps
      (Arlib.Computation.Charged.opMany
        (CountingMatroid.Model.Operations.Op.word instr) z result) = z := by
    cases instr <;> simp [otherSteps, Arlib.Computation.Op.all,
      Arlib.Computation.CostVec.many]
  rw [hcost]
  unfold binaryRatLength binaryNatLength
  apply Nat.pow_le_pow_left
  omega



/-- INTERNAL: A natural cast needs its own binary length plus three framing bits. -/
theorem binaryRatLength_natCast (a : ℕ) :
    binaryRatLength (a : ℚ) = a.log2 + 4 := by
  simp only [binaryRatLength, binaryNatLength, Rat.num_natCast,
    Rat.den_natCast, Int.natAbs_natCast]
  have h : (1 : ℕ).log2 = 0 := by decide
  rw [h]
  omega









end CountingMatroid.Analysis.ScheduleOtherStepsEnvelope

end
set_option autoImplicit false

/-!
The bounded-run nonoracle-work envelope is reduced to two single-phase
obligations: `phase_preserves_size` and `phase_otherSteps_le`. Their files
record the remaining multiplier-size and abort-path work proofs.

This module combines those statements by induction over the actual indexed
phase loop, bounds initialization, and proves the final-scaling work bound.
The full envelope is conditional on those two open child obligations; it is
not yet a completed resource proof. Existing power/count/height support is
still downstream in `BoundedRunResourceEnvelope` and needs upstream extraction
for use in the child proofs.
-/

namespace CountingMatroid.Analysis.BoundedRunOtherSteps
end CountingMatroid.Analysis.BoundedRunOtherSteps
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.BoundedRunOtherSteps
open CountingMatroid.Model
open CountingMatroid.Model.Subroutines

open CountingMatroid.Model.Operations CountingMatroid.Program
open CountingMatroid.Analysis.BoundedRunPhase
open CountingMatroid.Analysis.ResourceBound

/-- INTERNAL: Final scaling costs polynomial work in the dimension and the
already-bounded product length. The logarithmic fold invariant avoids treating
the exponentially large integer scale as a unary size.
TEXLINE: main.tex:1376-1390 -/
theorem solution {n : ℕ}
    (result : Option (AnnealingCursor n)) (K : ℕ)
    (hresult : ∀ current, result = some current → binaryRatLength current.product ≤ K) :
    otherSteps (match result with
      | none => pure ((0 : ℚ), (0 : ℕ))
      | some current => do
          let powerOfTwo ← natPower 2 n
          let scale ← ratOfNat powerOfTwo
          let estimate ← ratMul scale current.product
          pure (estimate, current.bitCursor)) ≤
      3 * n + 1 + (2 * n + 4 + K) ^ 2 := by
  cases result with
  | none => simp [otherSteps]
  | some current =>
      have hlogFold (l : List ℕ) (acc : ℕ) :
          (Arlib.Computation.Charged.foldl
            (fun value (_ : ℕ) => natMul value 2) l acc).val.log2 ≤
              acc.log2 + 2 * l.length := by
        induction l generalizing acc with
        | nil => simp
        | cons a l ih =>
            rw [Arlib.Computation.Charged.val_foldl_cons]
            have hmul := ScheduleOtherStepsEnvelope.log2_mul_le acc 2
            have htail := ih (acc * 2)
            simpa only [List.length_cons, natMul,
              Arlib.Computation.Charged.val_op] using
              (show (Arlib.Computation.Charged.foldl
                (fun value (_ : ℕ) => natMul value 2) l (acc * 2)).val.log2 ≤
                acc.log2 + 2 * (l.length + 1) by norm_num at hmul; omega)
      let a := (natPower 2 n).val
      have hlog : a.log2 ≤ 2 * n := by
        have hone : Nat.log2 1 = 0 := by decide
        simpa [a, natPower, Arlib.Computation.Charged.repeatFor, hone] using
          hlogFold (List.range n) 1
      have hcast : otherSteps (ratOfNat a) = a.log2 + 1 := by
        simp [otherSteps, ratOfNat, Arlib.Computation.Op.all,
          Arlib.Computation.CostVec.many]
      have hmul : otherSteps (ratMul (a : ℚ) current.product) ≤
          (binaryRatLength (a : ℚ) + binaryRatLength current.product) ^ 2 :=
        ScheduleOtherStepsEnvelope.rationalBinary_otherSteps_le .mul
          (a : ℚ) current.product ((a : ℚ) * current.product)
      rw [ScheduleOtherStepsEnvelope.binaryRatLength_natCast] at hmul
      have hp := hresult current rfl
      have hb : a.log2 + 4 + binaryRatLength current.product ≤ 2 * n + 4 + K := by
        omega
      have hm := hmul.trans (Nat.pow_le_pow_left hb 2)
      rw [otherSteps_bind, otherSteps_bind, otherSteps_bind]
      change otherSteps (natPower 2 n) +
        (otherSteps (ratOfNat a) + (otherSteps (ratMul (a : ℚ) current.product) + 0)) ≤ _
      rw [ScheduleOtherStepsEnvelope.natPower_otherSteps_eq, hcast]
      omega
