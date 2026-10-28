-- Prove2me | solution 1 for CountingMatroid.Analysis.ScheduleCostEnvelope.schedule_oracleCalls_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T13:13:14.327175+00:00
-- url     : https://prove2.me/submissions/fe3c495b-037d-423e-be1b-9f546fd2012c

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
import Theorems.Thm_CountingMatroid_Analysis_ScheduleCostEnvelope_leastDrawTrials_oracleCalls_zero
import Theorems.Thm_CountingMatroid_Analysis_ScheduleCostEnvelope_leastHalvings_oracleCalls_zero

namespace CountingMatroid.Analysis.ScheduleCostEnvelope
end CountingMatroid.Analysis.ScheduleCostEnvelope
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




/-- INTERNAL: Iterating oracle-free arithmetic preserves zero oracle cost. -/
theorem oracleCalls_foldl_zero {α β : Type}
    (f : β → α → Arlib.Computation.Charged Op Cell β)
    (hf : ∀ b a, oracleCalls (f b a) = 0) (l : List α) (b : β) :
    oracleCalls (Arlib.Computation.Charged.foldl f l b) = 0 := by
  induction l generalizing b with
  | nil => simp [oracleCalls]
  | cons a l ih =>
      simp only [Arlib.Computation.Charged.cost_foldl_cons, oracleCalls, Pi.add_apply]
      have hb := hf b a
      have hl := ih (f b a).val
      simp only [oracleCalls] at hb hl
      omega

/-- INTERNAL: A repeated natural multiplication never queries an oracle. -/
theorem natPower_oracleCalls_zero (base exponent : ℕ) :
    oracleCalls (CountingMatroid.Program.natPower base exponent) = 0 := by
  unfold CountingMatroid.Program.natPower Arlib.Computation.Charged.repeatFor
  apply oracleCalls_foldl_zero
  intro b a
  simp [oracleCalls, natMul, Arlib.Computation.CostVec.one]









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

set_option maxRecDepth 4096 in
/-- INTERNAL: Constructing the schedule makes no independence-oracle calls. -/
theorem solution (n : ℕ) (p : InputParams) :
    oracleCalls (CountingMatroid.Program.schedule n p) = 0 := by
  have hdiv (a b : ℚ) : oracleCalls (ratDiv a b) = 0 := by
    simp [oracleCalls, ratDiv, Arlib.Computation.CostVec.many]
  have hsub (a b : ℚ) : oracleCalls (ratSub a b) = 0 := by
    simp [oracleCalls, ratSub, Arlib.Computation.CostVec.many]
  have hmul (a b : ℚ) : oracleCalls (ratMul a b) = 0 := by
    simp [oracleCalls, ratMul, Arlib.Computation.CostVec.many]
  have hofNat (a : ℕ) : oracleCalls (ratOfNat a) = 0 := by
    simp [oracleCalls, ratOfNat, Arlib.Computation.CostVec.many]
  have hnatMul (a b : ℕ) : oracleCalls (natMul a b) = 0 := by
    simp [oracleCalls, natMul, Arlib.Computation.CostVec.one]
  have hnatAdd (a b : ℕ) : oracleCalls (natAdd a b) = 0 := by
    simp [oracleCalls, natAdd, Arlib.Computation.CostVec.one]
  have hsucc (a : ℕ) : oracleCalls (successor a) = 0 := by
    simp [oracleCalls, successor, Arlib.Computation.CostVec.one]
  have hceil (a : ℚ) : oracleCalls (rationalCeil a) = 0 := by
    simp [oracleCalls, rationalCeil, Arlib.Computation.CostVec.many]
  have hpure {α : Type} (a : α) :
      oracleCalls (pure a : Arlib.Computation.Charged Op Cell α) = 0 := by
    simp [oracleCalls]
  unfold CountingMatroid.Program.schedule
  simp only [oracleCalls_bind,
    natPower_oracleCalls_zero, leastHalvings_oracleCalls_zero,
    leastDrawTrials_oracleCalls_zero, hdiv, hsub, hmul, hofNat,
    hnatMul, hnatAdd, hsucc, hceil, hpure, Nat.zero_add]
