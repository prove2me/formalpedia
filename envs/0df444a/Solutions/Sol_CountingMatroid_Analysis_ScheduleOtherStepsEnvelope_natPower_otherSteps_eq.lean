-- Prove2me | solution 1 for CountingMatroid.Analysis.ScheduleOtherStepsEnvelope.natPower_otherSteps_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T12:57:45.10031+00:00
-- url     : https://prove2.me/submissions/4a27a7e3-a2e3-4b1c-87e5-ae591d86747a

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
section


set_option autoImplicit false

namespace CountingMatroid.Analysis.ScheduleOtherStepsEnvelope

open CountingMatroid.Model
open CountingMatroid.Model.Subroutines

/-- INTERNAL: The nonoracle charge is additive under charged sequencing. -/
private theorem otherSteps_bind {α β : Type}
    (q : Arlib.Computation.Charged CountingMatroid.Model.Operations.Op
      CountingMatroid.Model.Operations.Cell α)
    (f : α → Arlib.Computation.Charged CountingMatroid.Model.Operations.Op
      CountingMatroid.Model.Operations.Cell β) :
    otherSteps (q >>= f) = otherSteps q + otherSteps (f q.val) := by
  have fold_add (l : List Arlib.Computation.Op)
      (u v : Arlib.Computation.Op → ℕ) (a b : ℕ) :
      l.foldl (fun z x => z + (u x + v x)) (a + b) =
        l.foldl (fun z x => z + u x) a +
          l.foldl (fun z x => z + v x) b := by
    induction l generalizing a b with
    | nil => rfl
    | cons x xs ih =>
        simpa [List.foldl, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
          using ih (a + u x) (b + v x)
  simp only [otherSteps, Arlib.Computation.Charged.cost_bind, Pi.add_apply]
  have h := fold_add Arlib.Computation.Op.all
    (fun x => q.cost (CountingMatroid.Model.Operations.Op.word x))
    (fun x => (f q.val).cost (CountingMatroid.Model.Operations.Op.word x)) 0 0
  simp only [Nat.zero_add] at h
  rw [h]
  omega































end CountingMatroid.Analysis.ScheduleOtherStepsEnvelope

end
set_option autoImplicit false

namespace CountingMatroid.Analysis.ScheduleOtherStepsEnvelope
end CountingMatroid.Analysis.ScheduleOtherStepsEnvelope
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.ScheduleOtherStepsEnvelope

open CountingMatroid.Model
open CountingMatroid.Model.Subroutines

/-- INTERNAL: Each multiplication in a charged natural power costs one word step. -/
theorem solution (base exponent : ℕ) :
    otherSteps (CountingMatroid.Program.natPower base exponent) = exponent := by
  have hfold (l : List ℕ) (acc : ℕ) :
      otherSteps (Arlib.Computation.Charged.foldl
        (fun acc _ => CountingMatroid.Model.Operations.natMul acc base) l acc) =
        l.length := by
    induction l generalizing acc with
    | nil => simp [otherSteps]
    | cons x xs ih =>
        rw [show Arlib.Computation.Charged.foldl
          (fun acc _ => CountingMatroid.Model.Operations.natMul acc base)
          (x :: xs) acc =
          CountingMatroid.Model.Operations.natMul acc base >>= fun next =>
            Arlib.Computation.Charged.foldl
              (fun acc _ => CountingMatroid.Model.Operations.natMul acc base)
              xs next from rfl, otherSteps_bind]
        have hone : otherSteps (CountingMatroid.Model.Operations.natMul acc base) = 1 := by
          simp [otherSteps, CountingMatroid.Model.Operations.natMul,
            Arlib.Computation.CostVec.one, Arlib.Computation.Op.all]
        rw [hone, ih]
        simp only [List.length_cons]
        omega
  unfold CountingMatroid.Program.natPower Arlib.Computation.Charged.repeatFor
  simpa using hfold (List.range exponent) 1
