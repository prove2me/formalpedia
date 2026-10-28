-- Prove2me | solution 1 for CountingMatroid.Analysis.BoundedUniformAbortMass.abort_forces_leading_bits
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T16:01:02.629933+00:00
-- url     : https://prove2.me/submissions/83519fdd-c1f8-47f5-b1c6-c1cdec12717e

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
import Theorems.Thm_CountingMatroid_Analysis_BoundedUniformAbortMass_boundedUniform_value

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





/-- INTERNAL: A false leading bit makes a rejection word strictly less than
its positive nonsingleton denominator.
TEXLINE: main.tex:1394-1401 -/
theorem false_leading_bit_accepts (tape : ℕ → Bool) (v cursor : ℕ)
    (hv : 2 ≤ v) (hbit : tape cursor = false) :
    (readWord tape ((v - 1).log2 + 1) 0 cursor).1 < v := by
  simp only [readWord, hbit, Bool.false_eq_true, ite_false, mul_zero, zero_add]
  have h := readWord_lt tape (v - 1).log2 0 (cursor + 1)
  simp only [zero_add, one_mul] at h
  have hpow : 2 ^ (v - 1).log2 ≤ v - 1 := Nat.log2_self_le (by omega)
  omega



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

/-!
Finite-bit rejection-cap bounds for the actual charged integer sampler.
A rejected trial has a true leading bit: a false leading bit produces an
integer below the positive denominator. Distinct trials use disjoint words.
Coverage is an explicit premise here; obtaining it for adaptive calls in a
whole phase restart remains an obligation of the consuming analysis.
-/

namespace CountingMatroid.Analysis.BoundedUniformAbortMass
end CountingMatroid.Analysis.BoundedUniformAbortMass
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.BoundedUniformAbortMass

open CountingMatroid.Model CountingMatroid.Model.Operations CountingMatroid.Program

/-- INTERNAL: Exhausting the sampler cap forces a true leading bit in
every trial word. This is a necessary event, not a claim of uniform output.
TEXLINE: main.tex:1392-1421 -/
theorem solution (tape : ℕ → Bool) (trials v cursor : ℕ)
    (hv : 2 ≤ v)
    (habort : (boundedUniform tape trials v cursor).val.1 = none) :
    ∀ k < trials, tape (cursor + k * ((v - 1).log2 + 1)) = true := by
  rw [boundedUniform_value tape trials v cursor hv] at habort
  induction trials generalizing cursor with
  | zero => intro k hk; omega
  | succ trials ih =>
      simp only [sampleWords, Option.isSome_none, Bool.false_eq_true, ite_false] at habort
      have hrejected : ¬ (readWord tape ((v - 1).log2 + 1) 0 cursor).1 < v := by
        intro haccepted
        rw [if_pos haccepted, sampleWords_some] at habort
        contradiction
      rw [if_neg hrejected, readWord_cursor] at habort
      have hhead : tape cursor = true := by
        cases hbit : tape cursor with
        | false => exact False.elim (hrejected (false_leading_bit_accepts tape v cursor hv hbit))
        | true => rfl
      intro k hk
      cases k with
      | zero => simpa using hhead
      | succ k =>
          have ht := ih (cursor + ((v - 1).log2 + 1)) habort k (by omega)
          convert ht using 1
          congr 1
          ring
