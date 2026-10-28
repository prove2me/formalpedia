-- Prove2me | solution 1 for CountingMatroid.Analysis.BoundedUniformAbortMass.boundedUniform_value
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T15:37:59.798644+00:00
-- url     : https://prove2.me/submissions/3674c2be-4bac-47ce-8c60-d237845b2e50

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
import Theorems.Thm_CountingMatroid_Analysis_BoundedUniformAbortMass_readWord_charged

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

/-- INTERNAL: For a nonsingleton positive denominator, the charged sampler
is exactly the binary-word rejection loop.
TEXLINE: main.tex:1392-1401 -/
theorem solution (tape : ℕ → Bool) (trials v cursor : ℕ)
    (hv : 2 ≤ v) :
    (boundedUniform tape trials v cursor).val =
      sampleWords tape v trials (none, cursor) := by
  with_unfolding_all
    let step : Option ℕ × ℕ → Arlib.Computation.Charged Op Cell (Option ℕ × ℕ) :=
      fun acc => do
        let done ← isSome acc.1
        if done then pure acc else do
          let trial ← Arlib.Computation.Charged.repeatFor (fun _ (inner : ℕ × ℕ) => do
            let bit ← fairBit tape inner.2
            let value ← appendBit inner.1 bit
            let next ← successor inner.2
            pure (value, next)) ((v - 1).log2 + 1) (0, acc.2)
          let accepted ← lessThan trial.1 v
          if accepted then pure (some trial.1, trial.2)
          else pure (none, trial.2)
    have hstep (acc : Option ℕ × ℕ) :
        (step acc).val = if acc.1.isSome then acc else
          let word := readWord tape ((v - 1).log2 + 1) 0 acc.2
          if word.1 < v then (some word.1, word.2) else (none, word.2) := by
      rcases acc with ⟨value, cursor⟩
      cases value with
      | some value =>
          simp only [step, Arlib.Computation.Charged.val_bind, isSome,
            Arlib.Computation.Charged.val_op, Option.isSome_some,
            ite_true, Arlib.Computation.Charged.val_pure]
      | none =>
          simp only [step, Arlib.Computation.Charged.val_bind, isSome,
            Arlib.Computation.Charged.val_op, Option.isSome_none,
            Bool.false_eq_true, ite_false, readWord_charged]
          by_cases ha : (readWord tape ((v - 1).log2 + 1) 0 cursor).1 < v
          · simp only [lessThan, ha, decide_true, Arlib.Computation.Charged.val_op,
              ite_true, Arlib.Computation.Charged.val_pure]
          · simp only [lessThan, ha, decide_false, Arlib.Computation.Charged.val_op,
              Bool.false_eq_true, ite_false, Arlib.Computation.Charged.val_pure]
    have hfold (xs : List ℕ) (acc : Option ℕ × ℕ) :
        (Arlib.Computation.Charged.foldl (fun acc _ => step acc) xs acc).val =
          sampleWords tape v xs.length acc := by
      induction xs generalizing acc with
      | nil => rfl
      | cons x xs ih =>
          rw [Arlib.Computation.Charged.val_foldl_cons, hstep, ih]
          rfl
    have hbad : ¬ v < 1 := by omega
    have hsingle : ¬ v < 2 := by omega
    unfold boundedUniform
    simp only [Arlib.Computation.Charged.val_bind, lessThan, uniformWidth,
      Arlib.Computation.Charged.val_op, decide_eq_true_eq, hbad, hsingle,
      ite_false]
    simpa only [Arlib.Computation.Charged.repeatFor, List.length_range, step, lessThan] using
      hfold (List.range trials) (none, cursor)
