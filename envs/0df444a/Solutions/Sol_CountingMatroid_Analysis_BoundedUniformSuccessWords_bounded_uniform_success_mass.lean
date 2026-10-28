-- Prove2me | solution 1 for CountingMatroid.Analysis.BoundedUniformSuccessWords.bounded_uniform_success_mass
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T16:17:36.180473+00:00
-- url     : https://prove2.me/submissions/4f391eae-edfe-48a6-bab5-74823a6dcaff

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
import Theorems.Thm_CountingMatroid_Analysis_BoundedUniformSuccessWords_first_accepted_word_mass
import Theorems.Thm_CountingMatroid_Analysis_BoundedUniformSuccessWords_sample_words_success_iff

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

/-- INTERNAL: Joint value/cursor law for a successful capped integer draw.
Its k earlier rejection words contribute their exact cylinder count; the
unused suffix is unrestricted. This is an unnormalised successful mass.
TEXLINE: main.tex:1392-1401,1415-1421 -/
theorem solution (head : List Bool)
    (trials v t k value : ℕ) (hv : 2 ≤ v) (hk : k < trials) (ha : value < v)
    (hcover : (k + 1) * ((v - 1).log2 + 1) ≤ t) :
    FiniteStoppedFiberMass.fairMass head t (fun tape =>
      (boundedUniform tape trials v head.length).val =
        (some value, head.length + (k + 1) * ((v - 1).log2 + 1))) =
      ((2 ^ ((v - 1).log2 + 1) - v : ℕ) : ℝ) ^ k /
        (2 : ℝ) ^ ((k + 1) * ((v - 1).log2 + 1)) := by
  let width := (v - 1).log2 + 1
  have hw : 0 < width := by dsimp [width]; omega
  have hvword : v ≤ 2 ^ width := by
    have hb := Nat.lt_log2_self (n := v - 1)
    dsimp only [width]
    omega
  have hevent (tape : ℕ → Bool) :
      (boundedUniform tape trials v head.length).val =
          (some value, head.length + (k + 1) * width) ↔
      (readWord tape width 0 (head.length + k * width)).1 = value ∧
        ∀ j < k, v ≤ (readWord tape width 0 (head.length + j * width)).1 := by
    rw [bounded_uniform_success_words tape trials v head.length value _ hv]
    constructor
    · rintro ⟨j, _, hstop, _, hword, hrejected⟩
      have hj : j = k := by
        change head.length + (k + 1) * width = head.length + (j + 1) * width at hstop
        nlinarith
      subst j
      exact ⟨hword, hrejected⟩
    · rintro ⟨hword, hrejected⟩
      exact ⟨k, hk, rfl, ha, hword, hrejected⟩
  have hfun : (fun tape => (boundedUniform tape trials v head.length).val =
      (some value, head.length + (k + 1) * width)) =
      (fun tape => (readWord tape width 0 (head.length + k * width)).1 = value ∧
        ∀ j < k, v ≤ (readWord tape width 0 (head.length + j * width)).1) :=
    funext (fun tape => propext (hevent tape))
  change FiniteStoppedFiberMass.fairMass head t
    (fun tape => (boundedUniform tape trials v head.length).val =
      (some value, head.length + (k + 1) * width)) = _
  rw [hfun]
  exact first_accepted_word_mass head t width v k value hw hvword ha hcover
