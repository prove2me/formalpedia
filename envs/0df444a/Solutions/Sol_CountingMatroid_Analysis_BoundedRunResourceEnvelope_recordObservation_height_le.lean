-- Prove2me | solution 1 for CountingMatroid.Analysis.BoundedRunResourceEnvelope.recordObservation_height_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T12:56:36.118902+00:00
-- url     : https://prove2.me/submissions/0edb4234-6d2c-4109-9071-51deefc735f6

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
import Theorems.Thm_CountingMatroid_Analysis_BoundedRunResourceEnvelope_ratPower_binary_length_le
import Theorems.Thm_CountingMatroid_Analysis_RationalHeight_rationalHeight_add_le

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
namespace CountingMatroid.Analysis.BoundedRunResourceEnvelope
end CountingMatroid.Analysis.BoundedRunResourceEnvelope
section


set_option autoImplicit false

namespace CountingMatroid.Analysis.RationalHeight
open CountingMatroid.Model



/-- INTERNAL: Component height is bounded by the full encoding length. -/
theorem rationalHeight_le_length (q : ℚ) : rationalHeight q ≤ binaryRatLength q := by
  unfold rationalHeight binaryRatLength binaryNatLength
  omega






end CountingMatroid.Analysis.RationalHeight

end
set_option autoImplicit false

namespace CountingMatroid.Analysis.BoundedRunResourceEnvelope
end CountingMatroid.Analysis.BoundedRunResourceEnvelope
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.BoundedRunResourceEnvelope

open CountingMatroid.Model
open CountingMatroid.Model.Operations
open CountingMatroid.Model.Subroutines
open CountingMatroid.Analysis.RationalHeight

/-- INTERNAL: One observation has additive component-height growth, independently
of the state and of the supplied oracles. TEXLINE: main.tex:1362-1378 -/
theorem solution {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (rho : ℚ)
    (current next : CountingMatroid.Program.ObservationCursor n)
    (h : (CountingMatroid.Program.recordObservation r o₁ o₂ rho current).val =
      some next) : rationalHeight next.numeratorSum ≤ rationalHeight current.numeratorSum +
        (binaryRatLength 1 + n * binaryRatLength rho + 1) := by
  simp only [CountingMatroid.Program.recordObservation,
    Arlib.Computation.Charged.val_bind] at h
  split at h
  · simp at h
  · simp [countIncrement] at h
    subst next
    exact Nat.le_add_right _ _
  · simp only [Arlib.Computation.Charged.val_bind,
      Arlib.Computation.Charged.val_pure] at h
    cases Option.some.inj h
    simp only [ratAdd, Arlib.Computation.Charged.val_opMany,
      CountingMatroid.Model.Operations.natSub, Arlib.Computation.Charged.val_op]
    have hp := ratPower_binary_length_le rho
      (n - (pairedRank r o₁ o₂ current.state).val)
    have hh := rationalHeight_le_length
      (CountingMatroid.Program.ratPower rho
        (n - (pairedRank r o₁ o₂ current.state).val)).val
    have ha := rationalHeight_add_le current.numeratorSum
      (CountingMatroid.Program.ratPower rho
        (n - (pairedRank r o₁ o₂ current.state).val)).val
    have hm := Nat.mul_le_mul_right (binaryRatLength rho)
      (Nat.sub_le n (pairedRank r o₁ o₂ current.state).val)
    omega
