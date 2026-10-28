-- Prove2me | solution 1 for CountingMatroid.Analysis.OutputSupport.outputLaw_support_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T12:57:39.672925+00:00
-- url     : https://prove2.me/submissions/0be9d017-945b-45c2-a897-d412e702f153

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

namespace CountingMatroid.Analysis.OutputSupport
end CountingMatroid.Analysis.OutputSupport
namespace CountingMatroid.Meta
end CountingMatroid.Meta
namespace Arlib
end Arlib
set_option autoImplicit false

namespace CountingMatroid.Analysis.OutputSupport
end CountingMatroid.Analysis.OutputSupport
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.OutputSupport

open CountingMatroid.Model
open CountingMatroid.Model.Subroutines

/-- INTERNAL: Expand the support of the charged output law to a possible
execution of the charged algorithm. -/
theorem solution (solver : FeasibilityImplementation) (n r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (p : InputParams)
    (x : ℚ × ExecutionCost) :
    x ∈ (Model.Run.outputLaw solver n r o₁ o₂ p).support ↔
      ∃ run ∈ (Model.Run.algorithmLaw solver n r o₁ o₂ p).support,
        (run.val,
          { oracleCalls := oracleCalls run,
            bitOps := otherSteps run,
            randomBits := run.cost Operations.Op.fairBit }) = x := by
  change x ∈ (PMF.map
    (fun run : Arlib.Computation.Charged Operations.Op Operations.Cell ℚ =>
      (run.val,
        { oracleCalls := oracleCalls run,
          bitOps := otherSteps run,
          randomBits := run.cost Operations.Op.fairBit }))
    (Model.Run.algorithmLaw solver n r o₁ o₂ p)).support ↔ _
  exact PMF.mem_support_map_iff
      (fun run : Arlib.Computation.Charged Operations.Op Operations.Cell ℚ =>
        (run.val,
          { oracleCalls := oracleCalls run,
            bitOps := otherSteps run,
            randomBits := run.cost Operations.Op.fairBit }))
      (Model.Run.algorithmLaw solver n r o₁ o₂ p) x
