-- Prove2me | solution 1 for CountingMatroid.Analysis.ScheduleOtherStepsEnvelope.thermalSetup_otherSteps_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T13:10:16.05591+00:00
-- url     : https://prove2.me/submissions/bb6798ae-f615-4736-865a-661c61d04c7c

import Definitions.Def_CountingMatroidSupport_Computation_Charged
import Definitions.Def_CountingMatroidSupport_Computation_Charged_Extension1
import Definitions.Def_CountingMatroidSupport_Computation_Charged_Extension2
import Definitions.Def_CountingMatroidSupport_Computation_Cost
import Definitions.Def_CountingMatroidSupport_Computation_Dict
import Definitions.Def_CountingMatroidSupport_Computation_Heap
import Definitions.Def_CountingMatroidSupport_Computation_Machine
import Definitions.Def_CountingMatroidSupport_Computation_Num
import Definitions.Def_CountingMatroidSupport_Computation_Queue
import Definitions.Def_CountingMatroidSupport_Computation_Rand
import Definitions.Def_CountingMatroidSupport_Computation_Roster
import Definitions.Def_CountingMatroidSupport_Computation_Slot
import Definitions.Def_CountingMatroidSupport_Computation_Space
import Definitions.Def_CountingMatroidSupport_Computation_Std
import Definitions.Def_CountingMatroid_Analysis_EstimateMedianResource
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

namespace CountingMatroid.Analysis.LeastHalvingsCost
end CountingMatroid.Analysis.LeastHalvingsCost
namespace CountingMatroid.Analysis
end CountingMatroid.Analysis
namespace CountingMatroid.Meta
end CountingMatroid.Meta
namespace Arlib
end Arlib
section

set_option autoImplicit false
open CountingMatroid.Model
open CountingMatroid.Model.Operations
open CountingMatroid.Model.Subroutines
namespace CountingMatroid.Analysis.ScheduleOtherStepsEnvelope








/-- INTERNAL: A charged rational binary operation is bounded by the
binary lengths of its inputs. -/
theorem opening_rationalBinary_cost_le (instr : Arlib.Computation.Op)
    (a b result : ℚ) :
    otherSteps (Arlib.Computation.Charged.opMany
      (Op.word instr)
      ((a.num.natAbs.log2 + a.den.log2 + 3 +
        (b.num.natAbs.log2 + b.den.log2 + 3)) ^ 2) result) ≤
      (binaryRatLength a + binaryRatLength b) ^ 2 := by
  have hcost (z : ℕ) : otherSteps
      (Arlib.Computation.Charged.opMany (Op.word instr) z result) = z := by
    cases instr <;> simp [otherSteps, Arlib.Computation.Op.all,
      Arlib.Computation.CostVec.many]
  rw [hcost]
  unfold binaryRatLength binaryNatLength
  apply Nat.pow_le_pow_left
  omega



end CountingMatroid.Analysis.ScheduleOtherStepsEnvelope

end

section

set_option autoImplicit false
open CountingMatroid.Model
open CountingMatroid.Model.Operations
open CountingMatroid.Model.Subroutines
namespace CountingMatroid.Analysis.ScheduleOtherStepsEnvelope




/-- INTERNAL: One charged word operation contributes one nonoracle step. -/
private theorem wordOp_cost {α : Type} (instr : Arlib.Computation.Op) (x : α) :
    otherSteps (Arlib.Computation.Charged.op (Op.word instr) x) = 1 := by
  cases instr <;> simp [otherSteps, Arlib.Computation.Op.all,
    Arlib.Computation.CostVec.one]

/-- INTERNAL: A charged batch of word operations contributes its batch size. -/
private theorem wordMany_cost {α : Type} (instr : Arlib.Computation.Op)
    (z : ℕ) (x : α) :
    otherSteps (Arlib.Computation.Charged.opMany (Op.word instr) z x) = z := by
  cases instr <;> simp [otherSteps, Arlib.Computation.Op.all,
    Arlib.Computation.CostVec.many]

/-- INTERNAL: Returning a value contributes no charge. -/
private theorem pure_cost {α : Type} (x : α) :
    otherSteps (pure x : Arlib.Computation.Charged Op Cell α) = 0 := by
  simp [otherSteps]



/-- INTERNAL: Thermal setup has four unit word charges, one natural cast,
and one rational division. -/
theorem thermalSetup_cost_eq (n : ℕ) (p : InputParams)
    (head : ScheduleOpeningResult) :
    otherSteps (thermalSetup n p head) =
      4 + (32 * (head.twoN * (n + head.bε) + 1)).log2 + 1 +
        otherSteps (ratDiv p.ε
          (32 * (head.twoN * (n + head.bε) + 1) : ℚ)) := by
  unfold thermalSetup
  simp only [CountingMatroid.Analysis.ResourceBound.otherSteps_bind]
  simp only [natAdd, natMul, successor, ratOfNat,
    Arlib.Computation.Charged.val_op, Arlib.Computation.Charged.val_opMany]
  simp only [wordOp_cost, wordMany_cost]
  simp only [pure_cost, Nat.add_zero]
  norm_num [Nat.cast_mul, Nat.cast_add]
  omega




end CountingMatroid.Analysis.ScheduleOtherStepsEnvelope

end
set_option autoImplicit false
open CountingMatroid.Model
open CountingMatroid.Model.Operations
open CountingMatroid.Model.Subroutines
namespace CountingMatroid.Analysis.ScheduleOtherStepsEnvelope
end CountingMatroid.Analysis.ScheduleOtherStepsEnvelope
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.ScheduleOtherStepsEnvelope

/-- INTERNAL: Thermal setup cost is controlled by its denominator length. -/
theorem solution (n : ℕ) (p : InputParams)
    (head : ScheduleOpeningResult) :
    let D := 32 * (head.twoN * (n + head.bε) + 1)
    otherSteps (thermalSetup n p head) ≤
      5 + D.log2 + (binaryRatLength p.ε + binaryRatLength (D : ℚ)) ^ 2 := by
  dsimp only
  rw [thermalSetup_cost_eq]
  have h := opening_rationalBinary_cost_le Arlib.Computation.Op.udiv
    p.ε (32 * (head.twoN * (n + head.bε) + 1) : ℚ)
    (p.ε / (32 * (head.twoN * (n + head.bε) + 1) : ℚ))
  change otherSteps (ratDiv p.ε
    (32 * (head.twoN * (n + head.bε) + 1) : ℚ)) ≤
    (binaryRatLength p.ε +
      binaryRatLength (32 * (head.twoN * (n + head.bε) + 1) : ℚ)) ^ 2 at h
  norm_num [Nat.cast_mul, Nat.cast_add] at h ⊢
  omega
