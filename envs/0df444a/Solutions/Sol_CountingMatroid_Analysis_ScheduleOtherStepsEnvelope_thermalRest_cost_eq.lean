-- Prove2me | solution 1 for CountingMatroid.Analysis.ScheduleOtherStepsEnvelope.thermalRest_cost_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T13:03:11.796392+00:00
-- url     : https://prove2.me/submissions/dadcffbd-96da-4286-ac33-c1b4960d777a

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
/-!
# Cost of the schedule tail

The setup phases have separate checked cost bounds. This module proves an exact
cost identity for the charged powers, observation count, draw width, and confidence
repetition computation, and bounds their sum by the prescribed polynomial.
Intermediate encoding lengths are bounded using the shared length and capped-search
lemmas in `ScheduleCostPrimitives`.
-/

set_option autoImplicit false

namespace CountingMatroid.Analysis.ScheduleOtherStepsEnvelope
end CountingMatroid.Analysis.ScheduleOtherStepsEnvelope
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.ScheduleOtherStepsEnvelope

open CountingMatroid.Model
open CountingMatroid.Model.Subroutines

/-- INTERNAL: Expand the schedule tail into its four power computations,
unit word charges, rational operations, and two capped searches.
TEXLINE: main.tex:1348-1358 -/
theorem solution (n : ℕ) (p : InputParams) (t : ThermalResult) :
    let A := 10000000000 * t.LPlusOne * (CountingMatroid.Program.natPower n 14).val
    let R := 2000 * (CountingMatroid.Program.natPower t.LPlusOne 2).val *
      (CountingMatroid.Program.natPower n 2).val *
      (20 * (CountingMatroid.Program.natPower n 4).val * (n * t.LPlusOne + 2))
    let Q := (A : ℚ) / (t.eta * t.eta)
    otherSteps (thermalRest n p t) =
      otherSteps (CountingMatroid.Program.natPower n 4) +
      otherSteps (CountingMatroid.Program.natPower t.LPlusOne 2) +
      otherSteps (CountingMatroid.Program.natPower n 2) +
      otherSteps (CountingMatroid.Program.natPower n 14) + 14 + (A.log2 + 1) +
      otherSteps (CountingMatroid.Model.Operations.ratMul t.eta t.eta) +
      otherSteps (CountingMatroid.Model.Operations.ratDiv (A : ℚ) (t.eta * t.eta)) +
      otherSteps (CountingMatroid.Model.Operations.rationalCeil Q) +
      otherSteps (CountingMatroid.Program.leastDrawTrials
        (3 * t.L * (R + (CountingMatroid.Model.Operations.rationalCeil Q).val))) +
      otherSteps (CountingMatroid.Program.leastHalvings p.δ) := by
  have hop {α : Type} (i : Arlib.Computation.Op) (x : α) :
      otherSteps (Arlib.Computation.Charged.op
        (CountingMatroid.Model.Operations.Op.word i) x) = 1 := by
    cases i <;> simp [otherSteps, Arlib.Computation.Op.all,
      Arlib.Computation.CostVec.one]
  have hcast (a : ℕ) :
      otherSteps (CountingMatroid.Model.Operations.ratOfNat a) = a.log2 + 1 := by
    simp [CountingMatroid.Model.Operations.ratOfNat, otherSteps,
      Arlib.Computation.Op.all, Arlib.Computation.CostVec.many]
  have hpure (x : AnnealingSchedule) :
      otherSteps (pure x : Arlib.Computation.Charged
        CountingMatroid.Model.Operations.Op CountingMatroid.Model.Operations.Cell
        AnnealingSchedule) = 0 := by simp [otherSteps]
  dsimp only
  unfold thermalRest
  simp only [CountingMatroid.Analysis.ResourceBound.otherSteps_bind]
  simp only [CountingMatroid.Model.Operations.natAdd,
    CountingMatroid.Model.Operations.natMul, CountingMatroid.Model.Operations.successor,
    Arlib.Computation.Charged.val_op, hop, hcast, hpure]
  simp only [CountingMatroid.Model.Operations.ratOfNat,
    CountingMatroid.Model.Operations.ratMul, CountingMatroid.Model.Operations.ratDiv,
    Arlib.Computation.Charged.val_opMany]
  omega
