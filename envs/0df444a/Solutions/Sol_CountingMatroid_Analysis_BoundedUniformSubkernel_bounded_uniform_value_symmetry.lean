-- Prove2me | solution 1 for CountingMatroid.Analysis.BoundedUniformSubkernel.bounded_uniform_value_symmetry
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T16:20:11.028683+00:00
-- url     : https://prove2.me/submissions/b8e1404e-5892-4672-a44c-6ce9a8164f56

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
import Theorems.Thm_CountingMatroid_Analysis_BoundedUniformAbortMass_boundedUniform_value
import Theorems.Thm_CountingMatroid_Analysis_BoundedUniformSuccessWords_bounded_uniform_success_mass
import Theorems.Thm_CountingMatroid_Analysis_BoundedUniformSuccessWords_sample_words_success_iff
import Theorems.Thm_CountingMatroid_Analysis_FiniteStoppedFiberMass_fairMass_stop_sum

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
namespace CountingMatroid.Analysis.BoundedUniformSubkernel
end CountingMatroid.Analysis.BoundedUniformSubkernel
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



















/-- INTERNAL: A successful nonsingleton bounded draw has exactly k rejected
words followed by its returned value, and stops at that word's boundary.
TEXLINE: main.tex:1392-1401 -/
theorem bounded_uniform_success_words (tape : ℕ → Bool)
    (trials v start value stop : ℕ) (hv : 2 ≤ v) :
    (boundedUniform tape trials v start).val = (some value, stop) ↔
      ∃ k < trials,
        stop = start + (k + 1) * ((v - 1).log2 + 1) ∧
        value < v ∧
        (readWord tape ((v - 1).log2 + 1) 0
          (start + k * ((v - 1).log2 + 1))).1 = value ∧
        ∀ j < k, v ≤ (readWord tape ((v - 1).log2 + 1) 0
          (start + j * ((v - 1).log2 + 1))).1 := by
  rw [boundedUniform_value tape trials v start hv]
  exact sample_words_success_iff tape v trials start value stop









end CountingMatroid.Analysis.BoundedUniformSuccessWords

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* 2026-10-09 · proved · binary-word injectivity and finite-cardinality enumeration give the exact first-accepted-word cylinder mass. The sampler normal form identifies its stopping word uniquely, yielding the joint value/cursor law; successful interval replay and stopped_fiber_bound transfer a fresh-suffix continuation estimate. All declarations are proved.
-/

end
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-! Covered successful bounded draws are subuniform, including the zero-bit
singleton draw. The estimate sums all stopping cursors before composing a
fresh-suffix continuation. -/
namespace CountingMatroid.Analysis.BoundedUniformSubkernel
end CountingMatroid.Analysis.BoundedUniformSubkernel
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.BoundedUniformSubkernel
open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.FiniteStoppedFiberMass
open CountingMatroid.Analysis.BoundedUniformSuccessWords

/-- INTERNAL: Covered successes give equal mass to any two in-range values,
even when the suffix cuts off the last rejection word.
TEXLINE: main.tex:1392-1401 -/
theorem solution (head : List Bool)
    (trials v t a b : ℕ) (hv : 2 ≤ v) (ha : a < v) (hb : b < v) :
    fairMass head t (fun tape => ∃ stop, stop ≤ head.length + t ∧
      (boundedUniform tape trials v head.length).val = (some a, stop)) =
    fairMass head t (fun tape => ∃ stop, stop ≤ head.length + t ∧
      (boundedUniform tape trials v head.length).val = (some b, stop)) := by
  classical
  let draw := fun tape => (boundedUniform tape trials v head.length).val.1.map
    (fun value => (value, (boundedUniform tape trials v head.length).val.2))
  have hmap (tape : ℕ → Bool) (value stop : ℕ) :
      draw tape = some (value, stop) ↔
        (boundedUniform tape trials v head.length).val = (some value, stop) := by
    dsimp [draw]
    cases (boundedUniform tape trials v head.length).val with
    | mk choice cursor => cases choice <;> simp [Prod.mk.injEq]
  have hsplit (value : ℕ) := fairMass_stop_sum head t draw value (fun _ _ => True)
  simp only [and_true, hmap] at hsplit
  rw [hsplit a, hsplit b]
  apply Finset.sum_congr rfl
  intro stop _
  by_cases hform : ∃ k < trials,
      stop.val = head.length + (k + 1) * ((v - 1).log2 + 1)
  · obtain ⟨k, hk, hstop⟩ := hform
    have hc : (k + 1) * ((v - 1).log2 + 1) ≤ t := by omega
    rw [hstop, bounded_uniform_success_mass head trials v t k a hv hk ha hc,
      bounded_uniform_success_mass head trials v t k b hv hk hb hc]
  · have hz (value : ℕ) : fairMass head t (fun tape =>
        (boundedUniform tape trials v head.length).val = (some value, stop.val)) = 0 := by
      unfold fairMass
      apply Finset.sum_eq_zero
      intro bits _
      apply if_neg
      intro hrun
      obtain ⟨k, hk, hs, _⟩ :=
        (bounded_uniform_success_words _ trials v head.length value stop.val hv).mp hrun
      exact hform ⟨k, hk, hs⟩
    rw [hz a, hz b]
