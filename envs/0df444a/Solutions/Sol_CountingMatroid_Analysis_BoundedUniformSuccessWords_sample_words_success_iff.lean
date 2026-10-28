-- Prove2me | solution 1 for CountingMatroid.Analysis.BoundedUniformSuccessWords.sample_words_success_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T15:08:28.258424+00:00
-- url     : https://prove2.me/submissions/8e9a24e4-6ef4-42e9-9109-c28d5b7bfc35

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

namespace CountingMatroid.Analysis.FiniteObservationMarkov
end CountingMatroid.Analysis.FiniteObservationMarkov
namespace CountingMatroid.Analysis.FiniteTapePrefixBound
end CountingMatroid.Analysis.FiniteTapePrefixBound
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
namespace CountingMatroid.Analysis.BoundedUniformSuccessWords
end CountingMatroid.Analysis.BoundedUniformSuccessWords
section


set_option autoImplicit false

/-!
Finite-bit rejection-cap bounds for the actual charged integer sampler.
A rejected trial has a true leading bit: a false leading bit produces an
integer below the positive denominator. Distinct trials use disjoint words.
Coverage is an explicit premise here; obtaining it for adaptive calls in a
whole phase restart remains an obligation of the consuming analysis.
-/

namespace CountingMatroid.Analysis.BoundedUniformAbortMass

open CountingMatroid.Model CountingMatroid.Model.Operations CountingMatroid.Program



/-- INTERNAL: The word scan consumes exactly its fixed width. -/
theorem readWord_cursor (tape : ℕ → Bool) (k value cursor : ℕ) :
    (readWord tape k value cursor).2 = cursor + k := by
  induction k generalizing value cursor with
  | zero => rfl
  | succ k ih => simp only [readWord, ih]; omega









/-- INTERNAL: Once a rejection draw accepts, later trials leave it unchanged. -/
theorem sampleWords_some (tape : ℕ → Bool) (v k value cursor : ℕ) :
    sampleWords tape v k (some value, cursor) = (some value, cursor) := by
  induction k with
  | zero => rfl
  | succ k ih => simpa only [sampleWords, Option.isSome_some, ite_true] using ih


  














end CountingMatroid.Analysis.BoundedUniformAbortMass

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r26 · proved · identified the charged word and rejection loops, proved that every aborted trial has a true leading bit, counted the distinct forced coordinates, and transferred the resulting cap bound to covered prefix-free adaptive histories.
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

/-- INTERNAL: Exact first-accepted-word characterization of the absorbing
trial loop, including its stopping cursor.
TEXLINE: main.tex:1392-1401 -/
theorem solution (tape : ℕ → Bool)
    (v trials start value stop : ℕ) :
    sampleWords tape v trials (none, start) = (some value, stop) ↔
      ∃ k < trials,
        stop = start + (k + 1) * ((v - 1).log2 + 1) ∧
        value < v ∧
        (readWord tape ((v - 1).log2 + 1) 0
          (start + k * ((v - 1).log2 + 1))).1 = value ∧
        ∀ j < k, v ≤ (readWord tape ((v - 1).log2 + 1) 0
          (start + j * ((v - 1).log2 + 1))).1 := by
  let width := (v - 1).log2 + 1
  change sampleWords tape v trials (none, start) = (some value, stop) ↔
    ∃ k < trials, stop = start + (k + 1) * width ∧ value < v ∧
      (readWord tape width 0 (start + k * width)).1 = value ∧
      ∀ j < k, v ≤ (readWord tape width 0 (start + j * width)).1
  induction trials generalizing start with
  | zero => simp [sampleWords]
  | succ trials ih =>
    simp only [sampleWords, Option.isSome_none, Bool.false_eq_true, ite_false]
    by_cases ha : (readWord tape width 0 start).1 < v
    · rw [if_pos ha, sampleWords_some]
      constructor
      · intro h
        have hvalue := congrArg (fun p : Option ℕ × ℕ => p.1) h
        have hstop := congrArg (fun p : Option ℕ × ℕ => p.2) h
        have hv : (readWord tape width 0 start).1 = value := Option.some.inj hvalue
        refine ⟨0, by omega, ?_, ?_, ?_, ?_⟩
        · simpa only [Nat.zero_add, Nat.one_mul, readWord_cursor] using hstop.symm
        · simpa only [hv] using ha
        · simpa only [Nat.zero_mul, Nat.add_zero] using hv
        · intro j hj; omega
      · rintro ⟨k, hk, hc, hv, hword, hrejected⟩
        have hk0 : k = 0 := by
          by_contra hn
          have hr := hrejected 0 (by omega)
          simp only [Nat.zero_mul, Nat.add_zero] at hr
          omega
        subst k
        simp only [Nat.zero_mul, Nat.add_zero] at hword
        rw [readWord_cursor]
        simp only [Nat.zero_add, Nat.one_mul] at hc
        exact Prod.ext (congrArg some hword) hc.symm
    · rw [if_neg ha, readWord_cursor, ih]
      constructor
      · rintro ⟨k, hk, hc, hv, hword, hrejected⟩
        refine ⟨k + 1, by omega, ?_, hv, ?_, ?_⟩
        · calc
            stop = start + width + (k + 1) * width := hc
            _ = start + (k + 1 + 1) * width := by ring
        · convert hword using 1
          congr 2
          simp only [width]
          ring
        · intro j hj
          cases j with
          | zero => simpa only [Nat.zero_mul, Nat.add_zero] using Nat.le_of_not_gt ha
          | succ j =>
            have hr := hrejected j (by omega)
            convert hr using 1
            congr 2
            simp only [width]
            ring
      · rintro ⟨k, hk, hc, hv, hword, hrejected⟩
        have hkpos : 0 < k := by
          by_contra hn
          have hk0 : k = 0 := by omega
          subst k
          simp only [Nat.zero_mul, Nat.add_zero] at hword
          exact ha (hword ▸ hv)
        obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hkpos)
        refine ⟨j, by omega, ?_, hv, ?_, ?_⟩
        · calc
            stop = start + (j + 1 + 1) * width := hc
            _ = start + width + (j + 1) * width := by ring
        · convert hword using 1
          congr 2
          simp only [width, Nat.succ_eq_add_one]
          ring
        · intro i hi
          have hr := hrejected (i + 1) (by omega)
          convert hr using 1
          congr 2
          simp only [width]
          ring
