-- Prove2me | solution 1 for CountingMatroid.Analysis.ScheduleOtherStepsEnvelope.leastHalvings_value_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T13:00:37.383813+00:00
-- url     : https://prove2.me/submissions/9a873ce9-414a-4f0f-8b19-e464c342dbd0

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
import Theorems.Thm_CountingMatroid_Analysis_ScheduleOtherStepsEnvelope_foldlWhile_first_le

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
set_option autoImplicit false

namespace CountingMatroid.Analysis.ScheduleOtherStepsEnvelope
end CountingMatroid.Analysis.ScheduleOtherStepsEnvelope
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.ScheduleOtherStepsEnvelope

open CountingMatroid.Model
open CountingMatroid.Model.Subroutines

/-- INTERNAL: The halving counter cannot exceed the length of its capped search.
TEXLINE: main.tex:1348-1351 -/
theorem solution (q : ℚ) :
    (CountingMatroid.Program.leastHalvings q).val ≤ q.den.log2 + 8 := by
  have hstep (acc : ℕ × ℚ) (round : ℕ) (next : ℕ × ℚ) :
      (do
        let needsStep ← CountingMatroid.Model.Operations.ratLess q acc.2
        if needsStep then
          let b ← CountingMatroid.Model.Operations.successor acc.1
          let power ← CountingMatroid.Model.Operations.ratDiv acc.2 2
          pure (some (b, power))
        else pure none : Arlib.Computation.Charged
          CountingMatroid.Model.Operations.Op CountingMatroid.Model.Operations.Cell
          (Option (ℕ × ℚ))).val = some next → next.1 ≤ acc.1 + 1 := by
    by_cases h : q < acc.2
    · simp [CountingMatroid.Model.Operations.ratLess,
        CountingMatroid.Model.Operations.successor,
        CountingMatroid.Model.Operations.ratDiv, h]
      intro heq
      cases heq
      omega
    · simp [CountingMatroid.Model.Operations.ratLess, h]
  have hloop := foldlWhile_first_le
    (fun acc (_ : ℕ) => do
      let needsStep ← CountingMatroid.Model.Operations.ratLess q acc.2
      if needsStep then
        let b ← CountingMatroid.Model.Operations.successor acc.1
        let power ← CountingMatroid.Model.Operations.ratDiv acc.2 2
        pure (some (b, power))
      else pure none)
    (List.range (q.den.log2 + 8)) (0, (1 : ℚ))
    (fun acc round next => hstep acc round next)
  simpa [CountingMatroid.Program.leastHalvings,
    CountingMatroid.Model.Operations.binaryLoopBound,
    Arlib.Computation.Charged.repeatWhile] using hloop
