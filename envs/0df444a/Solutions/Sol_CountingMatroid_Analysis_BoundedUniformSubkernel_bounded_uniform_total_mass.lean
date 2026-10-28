-- Prove2me | solution 1 for CountingMatroid.Analysis.BoundedUniformSubkernel.bounded_uniform_total_mass
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T15:09:37.482018+00:00
-- url     : https://prove2.me/submissions/3bb37ad2-dd80-4840-8318-39e28049bd66

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

namespace CountingMatroid.Analysis.BoundedUniformSubkernel
end CountingMatroid.Analysis.BoundedUniformSubkernel
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

/-- INTERNAL: Summing over in-range values counts each successful draw at
most once; its capped successful law may have total mass below one. -/
theorem solution (head : List Bool) (trials v t : ℕ) :
    (∑ a : Fin v, fairMass head t (fun tape => ∃ stop,
      stop ≤ head.length + t ∧
      (boundedUniform tape trials v head.length).val = (some a.val, stop))) ≤ 1 := by
  classical
  unfold fairMass
  rw [Finset.sum_comm]
  calc
    _ ≤ ∑ _ : List.Vector Bool t, 1 / (2 : ℝ) ^ t := by
      apply Finset.sum_le_sum
      intro bits _
      let tape := finiteTape (head ++ bits.val)
      simp only
      by_cases he : ∃ a : Fin v, ∃ stop, stop ≤ head.length + t ∧
          (boundedUniform tape trials v head.length).val = (some a.val, stop)
      · obtain ⟨a, stop, hs, hrun⟩ := he
        rw [Finset.sum_eq_single a]
        · rw [if_pos ⟨stop, hs, hrun⟩]
        · intro b _ hba
          apply if_neg
          rintro ⟨stopB, _, hB⟩
          have hab : a.val = b.val := by
            have h := congrArg Prod.fst (hrun.symm.trans hB)
            exact Option.some.inj h
          exact hba (Fin.ext hab.symm)
        · simp
      · have hz : (∑ a : Fin v, if ∃ stop, stop ≤ head.length + t ∧
            (boundedUniform tape trials v head.length).val = (some a.val, stop)
            then 1 / (2 : ℝ) ^ t else 0) = 0 := by
          apply Finset.sum_eq_zero
          intro a _
          exact if_neg (fun h => he ⟨a, h⟩)
        calc
          _ = (∑ a : Fin v, if ∃ stop, stop ≤ head.length + t ∧
              (boundedUniform tape trials v head.length).val = (some a.val, stop)
              then 1 / (2 : ℝ) ^ t else 0) := by
            apply Finset.sum_congr rfl
            intro a _
            split_ifs <;> rfl
          _ = 0 := hz
          _ ≤ _ := by positivity
    _ = 1 := by simp [card_vector]
