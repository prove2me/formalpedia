-- Prove2me | solution 1 for CountingMatroid.Analysis.ScheduleCostEnvelope.leastDrawTrials_oracleCalls_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T12:52:03.919382+00:00
-- url     : https://prove2.me/submissions/9f1d200a-9dfd-447f-86e2-b63e983e063f

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
import Theorems.Thm_CountingMatroid_Analysis_ScheduleCostEnvelope_oracleCalls_foldlWhile_zero

namespace CountingMatroid.Analysis.ScheduleCostEnvelope
end CountingMatroid.Analysis.ScheduleCostEnvelope
namespace CountingMatroid.Analysis.ScheduleOtherStepsEnvelope
end CountingMatroid.Analysis.ScheduleOtherStepsEnvelope
namespace CountingMatroid.Analysis.LeastHalvingsCost
end CountingMatroid.Analysis.LeastHalvingsCost
namespace CountingMatroid.Analysis.ResourceBound
end CountingMatroid.Analysis.ResourceBound
namespace CountingMatroid.Analysis
end CountingMatroid.Analysis
namespace CountingMatroid.Meta
end CountingMatroid.Meta
namespace Arlib
end Arlib
section


set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace CountingMatroid.Analysis.ScheduleCostEnvelope

open CountingMatroid.Model
open CountingMatroid.Model.Operations
open CountingMatroid.Model.Subroutines

/-- INTERNAL: Oracle charges add across charged sequencing. -/
theorem oracleCalls_bind {α β : Type}
    (p : Arlib.Computation.Charged Op Cell α)
    (f : α → Arlib.Computation.Charged Op Cell β) :
    oracleCalls (p >>= f) = oracleCalls p + oracleCalls (f p.val) := by
  simp [oracleCalls, Pi.add_apply, Nat.add_assoc, Nat.add_left_comm]
















end CountingMatroid.Analysis.ScheduleCostEnvelope

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r10 · partial · proved zero oracle cost and reduced the target to the separate nonoracle schedule charge bound; scheduler handoff request was refused by the shell policy.
* r9 · open · zero oracle charges proved for bounded searches and natural powers; the full charged bound needs rational encoding estimates.
-/

end
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace CountingMatroid.Analysis.ScheduleCostEnvelope
end CountingMatroid.Analysis.ScheduleCostEnvelope
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.ScheduleCostEnvelope

open CountingMatroid.Model
open CountingMatroid.Model.Operations
open CountingMatroid.Model.Subroutines

/-- INTERNAL: The drawing-width search only executes word operations. -/
theorem solution (M : ℕ) :
    oracleCalls (CountingMatroid.Program.leastDrawTrials M) = 0 := by
  have hstep : ∀ b : ℕ × ℕ, ∀ a : ℕ,
      oracleCalls (do
        let needsStep ← lessThan b.2 (32 * M)
        if needsStep then
          let count ← successor b.1
          let power ← natMul b.2 2
          pure (some (count, power))
        else pure none) = 0 := by
    intro b a
    by_cases h : b.2 < 32 * M <;>
      simp [oracleCalls, lessThan, successor, natMul, h,
        Arlib.Computation.CostVec.one]
  have hfold := oracleCalls_foldlWhile_zero
    (fun b (_ : ℕ) => do
      let needsStep ← lessThan b.2 (32 * M)
      if needsStep then
        let count ← successor b.1
        let power ← natMul b.2 2
        pure (some (count, power))
      else pure none) hstep
    (List.range (M.log2 + 8)) (1, 2)
  unfold CountingMatroid.Program.leastDrawTrials
  simp only [oracleCalls_bind, Arlib.Computation.Charged.repeatWhile]
  simpa [oracleCalls, binaryLoopBound, natMul,
    Arlib.Computation.CostVec.one] using hfold
