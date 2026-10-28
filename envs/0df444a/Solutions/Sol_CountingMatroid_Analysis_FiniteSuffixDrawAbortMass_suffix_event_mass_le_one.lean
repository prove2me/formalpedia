-- Prove2me | solution 1 for CountingMatroid.Analysis.FiniteSuffixDrawAbortMass.suffix_event_mass_le_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T15:14:29.750422+00:00
-- url     : https://prove2.me/submissions/c9979ee7-453b-4ea3-ba2a-ab513d5f353b

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
import Definitions.Def_CountingMatroid_Analysis_BoundedRunPhaseHistory
import Definitions.Def_CountingMatroid_Analysis_BoundedUniformAbortMass
import Definitions.Def_CountingMatroid_Analysis_BoundedUniformReplay
import Definitions.Def_CountingMatroid_Analysis_FiniteSuffixDrawAbortMass
import Definitions.Def_CountingMatroid_Analysis_FirstPhaseFailure
import Definitions.Def_CountingMatroid_Analysis_RelativeObservationBounds
import Definitions.Def_CountingMatroid_Analysis_ScheduleConfidence
import Definitions.Def_CountingMatroid_Analysis_TransversalPartition
import Definitions.Def_CountingMatroid_Analysis_TransversalProjection
import Definitions.Def_CountingMatroid_Interface_Pseudocode
import Definitions.Def_CountingMatroid_Interface_Pseudocode_Extension1
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
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Combinatorics.Matroid.Rank.ENat
import Mathlib.Data.BitVec
import Mathlib.Data.ENNReal.Inv
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Infix
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Sort
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Card.Arithmetic
import Mathlib.Data.Set.Finite.List
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Ring.RingNF

namespace CountingMatroid.Analysis.FiniteTapePrefixBound
end CountingMatroid.Analysis.FiniteTapePrefixBound
namespace CountingMatroid.Analysis.FiniteObservationMarkov
end CountingMatroid.Analysis.FiniteObservationMarkov
namespace CountingMatroid.Analysis.InitialRestartLaw
end CountingMatroid.Analysis.InitialRestartLaw
namespace CountingMatroid.Interface
end CountingMatroid.Interface
namespace CountingMatroid.Meta
end CountingMatroid.Meta
namespace Arlib
end Arlib
namespace CountingMatroid.Analysis.TransversalRankBridge
end CountingMatroid.Analysis.TransversalRankBridge
namespace CountingMatroid.Analysis.GreedyRankCorrect
end CountingMatroid.Analysis.GreedyRankCorrect
section


set_option autoImplicit false

/-!
Finite fair-bit conditioning by a consumed prefix. Appending a fixed prefix
is a bijection on its suffix event; disjoint consumed-prefix cylinders let
uniform suffix estimates transfer to the whole finite tape. This module
proves only counting facts, not the program's stopping-prefix property or
the phase's conditional analytic estimate.
-/

namespace CountingMatroid.Analysis.FiniteTapePrefixBound

/-- INTERNAL: There are exactly `2^m` Boolean tapes of length `m`.
TEXLINE: main.tex:1392-1421 -/
theorem fair_lists_ncard (m : ℕ) :
    Set.ncard {bits : List Bool | bits.length = m} = 2 ^ m := by
  change Nat.card (List.Vector Bool m) = _
  rw [Nat.card_eq_fintype_card, card_vector]
  simp













end CountingMatroid.Analysis.FiniteTapePrefixBound

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r19 · proved · Boolean tape count, fixed-prefix event bijection and mass, stopping-prefix freeness, prefix-cylinder disjointness, total prefix mass bound, and transfer of uniform suffix bounds. These counting results are used by `FiniteTapeLowerTail`; actual successful-history replay and analytic phase bounds are separate obligations.
-/

end
set_option autoImplicit false

/-!
Finite fair-suffix rejection bounds for the actual charged integer sampler.
The single-call bound uses the proved forced-leading-bit count for covered
rejection trials. The prefix-cylinder transfer below separates this stochastic
bound from the program's reachability and finite-block coverage proof.
-/

namespace CountingMatroid.Analysis.FiniteSuffixDrawAbortMass
end CountingMatroid.Analysis.FiniteSuffixDrawAbortMass
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.FiniteSuffixDrawAbortMass

open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.FiniteTapePrefixBound

/-- INTERNAL: Any event on a fixed-length fair Boolean suffix has mass at
most one. This also handles a rejection cap of zero. -/
theorem solution (t : ℕ) (E : List Bool → Prop) :
    (Set.ncard {bits : List Bool | bits.length = t ∧ E bits} : ENNReal) *
      (1 / 2 : ENNReal) ^ t ≤ 1 := by
  have hc : Set.ncard {bits : List Bool | bits.length = t ∧ E bits} ≤ 2 ^ t := by
    rw [← fair_lists_ncard t]
    exact Set.ncard_le_ncard (fun _ h => h.1) (List.finite_length_eq Bool t)
  calc
    _ ≤ ((2 ^ t : ℕ) : ENNReal) * (1 / 2 : ENNReal) ^ t := by
      exact mul_le_mul_left (Nat.cast_le.mpr hc) _
    _ = 1 := by
      rw [Nat.cast_pow, Nat.cast_ofNat, ← mul_pow]
      have htwo : (2 : ENNReal) * (1 / 2) = 1 := by
        rw [div_eq_mul_inv, one_mul]
        exact ENNReal.mul_inv_cancel (by norm_num) (by simp)
      rw [htwo, one_pow]
