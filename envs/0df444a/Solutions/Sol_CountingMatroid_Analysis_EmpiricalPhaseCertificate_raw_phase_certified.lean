-- Prove2me | solution 1 for CountingMatroid.Analysis.EmpiricalPhaseCertificate.raw_phase_certified
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T14:16:35.748713+00:00
-- url     : https://prove2.me/submissions/48a78a3a-351b-44cd-80e1-8e30c61f7b2c

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
import Definitions.Def_CountingMatroid_Analysis_EmpiricalPhaseCertificate
import Definitions.Def_CountingMatroid_Analysis_EstimateMedianResource
import Definitions.Def_CountingMatroid_Analysis_FinishPhaseEmpiricalUpdate
import Definitions.Def_CountingMatroid_Analysis_FirstPhaseFailure
import Definitions.Def_CountingMatroid_Analysis_PhaseResourcePrimitives
import Definitions.Def_CountingMatroid_Analysis_RationalHeight
import Definitions.Def_CountingMatroid_Analysis_RelativeObservationBounds
import Definitions.Def_CountingMatroid_Analysis_ScheduleConfidence
import Definitions.Def_CountingMatroid_Analysis_ScheduleOpeningCost
import Definitions.Def_CountingMatroid_Analysis_ScheduleThermalSetupCost
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
import Theorems.Thm_CountingMatroid_Analysis_EmpiricalPhaseCertificate_observation_estimates_finish

namespace CountingMatroid.Meta
end CountingMatroid.Meta
namespace Arlib
end Arlib
namespace CountingMatroid.Analysis.ScheduleOtherStepsEnvelope
end CountingMatroid.Analysis.ScheduleOtherStepsEnvelope
namespace CountingMatroid.Analysis.LeastHalvingsCost
end CountingMatroid.Analysis.LeastHalvingsCost
namespace CountingMatroid.Analysis
end CountingMatroid.Analysis
namespace CountingMatroid.Interface
end CountingMatroid.Interface
namespace CountingMatroid.Analysis.TransversalRankBridge
end CountingMatroid.Analysis.TransversalRankBridge
namespace CountingMatroid.Analysis.GreedyRankCorrect
end CountingMatroid.Analysis.GreedyRankCorrect
set_option autoImplicit false

namespace CountingMatroid.Analysis.EmpiricalPhaseCertificate
end CountingMatroid.Analysis.EmpiricalPhaseCertificate
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.EmpiricalPhaseCertificate

open CountingMatroid.Model CountingMatroid.Model.Operations CountingMatroid.Program
open CountingMatroid.Analysis.RelativeObservationBounds
open CountingMatroid.Analysis.FinishPhaseEmpiricalUpdate

/-- INTERNAL: Raw restart/observation estimates certify the actual phase,
including its product and stored-table updates. The stochastic bound can
therefore target raw estimation errors rather than assume learned weights
and accurate finish results simultaneously.
TEXLINE: main.tex:1253-1285 -/
theorem solution {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (tape : ℕ → Bool) (s : AnnealingSchedule) (j : ℕ)
    (hη : 0 ≤ s.η) (hηsmall : s.η ≤ 1 / 3)
    (hraw : RawPhaseEstimates r o₁ o₂ tape s j) :
    FirstPhaseFailure.CertifiedPhase r o₁ o₂ tape s j := by
  obtain ⟨current, start, observed, hcurrent, hgood, hstart, hobs, hest⟩ := hraw
  obtain ⟨ratio, nextWeights, hfinish, hl, hu, hnextGood⟩ :=
    observation_estimates_finish s j current.currentWeights observed _ _ _
      hη hηsmall hest
  let next : AnnealingCursor n :=
    ⟨if j + 1 < s.L then
        (learnedWeightWrite current.tables (j + 1) s.L nextWeights).val
      else current.tables,
      nextWeights, current.product * ratio, observed.bitCursor⟩
  refine ⟨ratio, hl, hu, current, next, hcurrent, ?_, rfl, hgood, ?_⟩
  · simp only [BoundedRunPhase.boundedRunPhase, Arlib.Computation.Charged.val_bind,
      CountingMatroid.Analysis.BoundedRunResourceEnvelope.ratPower_value_import_support, hstart, hobs, hfinish,
      ratMul, successor, lessThan, Arlib.Computation.Charged.val_opMany,
      Arlib.Computation.Charged.val_op]
    by_cases hj : j + 1 < s.L <;> simp [hj, next]
  · intro hj
    have htables := hgood.1
    have hw := hnextGood hj
    constructor
    · intro a ha index
      dsimp [next]
      rw [if_pos hj]
      simp only [learnedWeightWrite, Arlib.Computation.Charged.val_opMany]
      by_cases heq : a = j + 1
      · subst a
        simpa using hw index
      · rw [if_neg heq]
        exact htables a (by omega) index
    · exact hw
