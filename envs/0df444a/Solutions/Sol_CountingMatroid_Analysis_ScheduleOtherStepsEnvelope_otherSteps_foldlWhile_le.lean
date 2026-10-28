-- Prove2me | solution 1 for CountingMatroid.Analysis.ScheduleOtherStepsEnvelope.otherSteps_foldlWhile_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T13:00:53.271982+00:00
-- url     : https://prove2.me/submissions/d463f482-e2e7-49c5-a58d-b9b352cfdef7

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

/-- INTERNAL: A charged loop that may stop early costs at most its cap times
the cost of one round. -/
theorem solution {α β : Type}
    (f : β → α → Arlib.Computation.Charged
      CountingMatroid.Model.Operations.Op CountingMatroid.Model.Operations.Cell (Option β))
    (l : List α) (b : β) (k : ℕ)
    (h : ∀ b a, otherSteps (f b a) ≤ k) :
    otherSteps (Arlib.Computation.Charged.foldlWhile f l b) ≤ l.length * k := by
  induction l generalizing b with
  | nil => simp [otherSteps]
  | cons a l ih =>
      cases hv : (f b a).val with
      | none =>
          simp only [Arlib.Computation.Charged.val] at hv
          have heq : otherSteps (Arlib.Computation.Charged.foldlWhile f (a :: l) b) =
              otherSteps (f b a) := by
            simp [otherSteps, Arlib.Computation.Charged.foldlWhile, hv,
              Arlib.Computation.Charged.cost]
          rw [heq]
          calc otherSteps (f b a) ≤ k := h b a
            _ ≤ (a :: l).length * k := by
              simpa [List.length_cons] using
                (Nat.le_mul_of_pos_left k (Nat.succ_pos l.length))
      | some b' =>
          simp only [Arlib.Computation.Charged.val] at hv
          have hcost : (Arlib.Computation.Charged.foldlWhile f (a :: l) b).cost =
              (f b a).cost + (Arlib.Computation.Charged.foldlWhile f l b').cost := by
            simp [Arlib.Computation.Charged.foldlWhile, hv,
              Arlib.Computation.Charged.cost]
          have heq : otherSteps (Arlib.Computation.Charged.foldlWhile f (a :: l) b) =
              otherSteps (f b a) +
                otherSteps (Arlib.Computation.Charged.foldlWhile f l b') := by
            calc
              otherSteps (Arlib.Computation.Charged.foldlWhile f (a :: l) b) =
                  otherSteps ((f b a) >>= fun _ =>
                    Arlib.Computation.Charged.foldlWhile f l b') := by
                    simp only [otherSteps, hcost, Arlib.Computation.Charged.cost_bind,
                      Pi.add_apply]
              _ = _ := by rw [otherSteps_bind]
          rw [heq]
          have htail := ih b'
          have hhead := h b a
          simpa [List.length_cons, Nat.succ_mul, Nat.add_comm, Nat.add_left_comm,
            Nat.add_assoc] using Nat.add_le_add hhead htail
