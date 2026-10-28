-- Prove2me | solution 1 for CountingMatroid.Analysis.BoundedUniformSuccessWords.read_word_value_eq_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T15:09:00.276776+00:00
-- url     : https://prove2.me/submissions/025b3ce7-6548-4a15-ace9-ed4d425c3958

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
import Definitions.Def_CountingMatroid_Analysis_ChainStepIntervalReplay
import Definitions.Def_CountingMatroid_Analysis_FiniteStoppedFiberMass
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
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
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
import Mathlib.Data.Fintype.Vector
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
import Mathlib.Order.Interval.Finset.Fin
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

namespace CountingMatroid.Analysis.BoundedUniformSuccessWords
end CountingMatroid.Analysis.BoundedUniformSuccessWords
namespace CountingMatroid.Meta
end CountingMatroid.Meta
namespace Arlib
end Arlib
namespace CountingMatroid.Analysis.FiniteObservationMarkov
end CountingMatroid.Analysis.FiniteObservationMarkov
namespace CountingMatroid.Analysis.FiniteTapePrefixBound
end CountingMatroid.Analysis.FiniteTapePrefixBound
namespace CountingMatroid.Analysis.InitialRestartLaw
end CountingMatroid.Analysis.InitialRestartLaw
namespace CountingMatroid.Interface
end CountingMatroid.Interface
namespace CountingMatroid.Analysis.TransversalRankBridge
end CountingMatroid.Analysis.TransversalRankBridge
namespace CountingMatroid.Analysis.GreedyRankCorrect
end CountingMatroid.Analysis.GreedyRankCorrect
section


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-!
Successful capped integer draws are characterized by their first accepted
word. The characterization records both the returned integer and the consumed
cursor, with all earlier fixed-width words rejected. Binary-word enumeration
counts the corresponding finite fair-bit cylinders exactly. Interval replay
then transfers fresh-suffix continuation bounds at each successful endpoint.
-/

namespace CountingMatroid.Analysis.BoundedUniformSuccessWords

open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.BoundedUniformAbortMass

/-- INTERNAL: The fixed-width word scan adds its initial accumulator times
its binary place value to the value of the newly read bits.
TEXLINE: main.tex:1392-1401 -/
theorem read_word_accumulator (tape : ℕ → Bool) (width value start : ℕ) :
    (readWord tape width value start).1 =
      value * 2 ^ width + (readWord tape width 0 start).1 := by
  induction width generalizing value start with
  | zero => simp [readWord]
  | succ width ih =>
    simp only [readWord]
    rw [ih (2 * value + if tape start then 1 else 0) (start + 1),
      ih (2 * 0 + if tape start then 1 else 0) (start + 1), pow_succ]
    ring



























end CountingMatroid.Analysis.BoundedUniformSuccessWords

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* 2026-10-09 · proved · binary-word injectivity and finite-cardinality enumeration give the exact first-accepted-word cylinder mass. The sampler normal form identifies its stopping word uniquely, yielding the joint value/cursor law; successful interval replay and stopped_fiber_bound transfer a fresh-suffix continuation estimate. All declarations are proved.
-/

end
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-!
Successful capped integer draws are characterized by their first accepted
word. The characterization records both the returned integer and the consumed
cursor, with all earlier fixed-width words rejected. Binary-word enumeration
counts the corresponding finite fair-bit cylinders exactly. Interval replay
then transfers fresh-suffix continuation bounds at each successful endpoint.
-/

namespace CountingMatroid.Analysis.BoundedUniformSuccessWords
end CountingMatroid.Analysis.BoundedUniformSuccessWords
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.BoundedUniformSuccessWords

open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.BoundedUniformAbortMass

/-- INTERNAL: Equal fixed-width binary values identify every bit in the
consumed word; conversely, equal word bits give equal values.
TEXLINE: main.tex:1392-1401 -/
theorem solution (tape other : ℕ → Bool) (width start : ℕ) :
    (readWord tape width 0 start).1 = (readWord other width 0 start).1 ↔
      ∀ i, start ≤ i → i < start + width → tape i = other i := by
  induction width generalizing start with
  | zero =>
    simp only [readWord, Nat.add_zero, true_iff]
    intro i hlo hhi
    omega
  | succ width ih =>
    have ht := readWord_lt tape width 0 (start + 1)
    have ho := readWord_lt other width 0 (start + 1)
    simp only [Nat.zero_add, Nat.one_mul] at ht ho
    have hvalue : (readWord tape (width + 1) 0 start).1 =
        (if tape start then 1 else 0) * 2 ^ width +
          (readWord tape width 0 (start + 1)).1 := by
      simpa only [readWord, Nat.mul_zero, Nat.zero_add] using
        read_word_accumulator tape width (if tape start then 1 else 0) (start + 1)
    have hother : (readWord other (width + 1) 0 start).1 =
        (if other start then 1 else 0) * 2 ^ width +
          (readWord other width 0 (start + 1)).1 := by
      simpa only [readWord, Nat.mul_zero, Nat.zero_add] using
        read_word_accumulator other width (if other start then 1 else 0) (start + 1)
    rw [hvalue, hother]
    constructor
    · intro h
      have hb : tape start = other start := by
        cases hb : tape start <;> cases hc : other start <;>
          simp only [hb, hc, Bool.false_eq_true, ite_false, ite_true,
            Nat.zero_mul, Nat.zero_add, Nat.one_mul] at h ⊢ <;> omega
      have htail : (readWord tape width 0 (start + 1)).1 =
          (readWord other width 0 (start + 1)).1 := by
        rw [hb] at h
        omega
      have hagree := (ih (start + 1)).mp htail
      intro i hlo hhi
      by_cases hi : i = start
      · subst i; exact hb
      · exact hagree i (by omega) (by omega)
    · intro h
      have hb := h start le_rfl (by omega)
      have htail := (ih (start + 1)).mpr (fun i hlo hhi =>
        h i (by omega) (by omega))
      rw [hb, htail]
