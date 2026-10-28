-- Prove2me | solution 1 for CountingMatroid.Analysis.BoundedUniformSubkernel.bounded_uniform_stopped_continuation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T16:24:53.529876+00:00
-- url     : https://prove2.me/submissions/3cd97f22-edcb-40d0-b74e-2fea5e808b59

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
import Theorems.Thm_CountingMatroid_Analysis_BoundedUniformReplay_boundedUniform_interval_replay
import Theorems.Thm_CountingMatroid_Analysis_BoundedUniformSubkernel_bounded_uniform_covered_mass
import Theorems.Thm_CountingMatroid_Analysis_FiniteStoppedFiberMass_stopped_next_bound

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























/-- INTERNAL: Converting the sampler's optional value and retained cursor
into an optional pair preserves every successful value/cursor equality. -/
private theorem uniform_pair_map_eq (draw : Option ℕ × ℕ) (value stop : ℕ) :
    draw.1.map (fun a => (a, draw.2)) = some (value, stop) ↔
      draw = (some value, stop) := by
  rcases draw with ⟨choice, cursor⟩
  cases choice <;> simp [Prod.mk.injEq]

/-- INTERNAL: Successful integer draws replay on their consumed interval
when the retained cursor is packaged with the optional successful value.
TEXLINE: main.tex:1392-1401,1415-1421 -/
theorem bounded_uniform_success_interval (trials v start : ℕ) :
    ChainStepIntervalReplay.SuccessReplay (fun tape =>
      (boundedUniform tape trials v start).val.1.map
        (fun a => (a, (boundedUniform tape trials v start).val.2)))
      Prod.snd start := by
  intro tape out hrun
  have hp := (uniform_pair_map_eq _ out.1 out.2).mp hrun
  have hr := BoundedUniformReplay.boundedUniform_interval_replay trials v start tape
  refine ⟨?_, ?_⟩
  · simpa only [hp] using hr.1
  · intro other hagree
    apply (uniform_pair_map_eq _ out.1 out.2).mpr
    exact (hr.2 other (by simpa only [hp] using hagree)).trans hp



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

/-- INTERNAL: Covered capped draws followed by a uniformly bounded fresh
continuation cost at most 1/v times that continuation bound, summed over
all possible endpoints rather than at one fixed endpoint.
TEXLINE: main.tex:1392-1401,1415-1421 -/
theorem solution (head : List Bool)
    (trials v t value : ℕ) (hv : 0 < v) (ha : value < v)
    (E : (ℕ → Bool) → ℕ → Prop) (B : ℝ) (hB : 0 ≤ B)
    (hcont : ∀ stop, head.length ≤ stop → stop ≤ head.length + t →
      ∀ pref : List.Vector Bool (stop - head.length),
      (boundedUniform (finiteTape (head ++ pref.val)) trials v head.length).val =
        (some value, stop) →
      fairMass (head ++ pref.val) (t - (stop - head.length))
        (fun tape => E tape stop) ≤ B) :
    fairMass head t (fun tape => ∃ stop, stop ≤ head.length + t ∧
      (boundedUniform tape trials v head.length).val = (some value, stop) ∧
      E tape stop) ≤ (1 / (v : ℝ)) * B := by
  let draw := fun tape => (boundedUniform tape trials v head.length).val.1.map
    (fun value => (value, (boundedUniform tape trials v head.length).val.2))
  have hmap (tape : ℕ → Bool) (a stop : ℕ) :
      draw tape = some (a, stop) ↔
        (boundedUniform tape trials v head.length).val = (some a, stop) := by
    dsimp [draw]
    cases (boundedUniform tape trials v head.length).val with
    | mk choice cursor => cases choice <;> simp [Prod.mk.injEq]
  have hbound := stopped_next_bound head t draw
    (bounded_uniform_success_interval trials v head.length) value E B hB (by
      intro stop hlo hhi pref hrun
      exact hcont stop hlo hhi pref ((hmap _ _ _).mp hrun))
  simp only [hmap] at hbound
  exact hbound.trans (mul_le_mul_of_nonneg_right
    (bounded_uniform_covered_mass head trials v t value hv ha) hB)
