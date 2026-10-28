-- Prove2me | solution 1 for CountingMatroid.Analysis.EmpiricalPhaseCertificate.observation_estimates_finish
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T14:14:38.037017+00:00
-- url     : https://prove2.me/submissions/28256089-2747-461e-86be-6a4fd77b677d

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
import Theorems.Thm_CountingMatroid_Analysis_FinishPhaseEmpiricalUpdate_finishPhase_empirical_update
import Theorems.Thm_CountingMatroid_Analysis_RelativeObservationBounds_learned_multiplier_bounds
import Theorems.Thm_CountingMatroid_Analysis_RelativeObservationBounds_relative_quotient_bounds

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

/-- INTERNAL: Raw correlated-observation estimates imply a successful actual
finish, an accurate ratio, and good next weights. This separates deterministic
learning from concentration and the finite-tape coupling.
TEXLINE: main.tex:1253-1270 -/
theorem solution {n : ℕ} (s : AnnealingSchedule) (j : ℕ)
    (weights : Multipliers n) (observed : ObservationCursor n)
    (R : ℚ) (ideal nextIdeal : Multipliers n)
    (hη : 0 ≤ s.η) (hηsmall : s.η ≤ 1 / 3)
    (hobs : ObservationEstimates s weights observed R ideal nextIdeal) :
    ∃ ratio : ℚ, ∃ nextWeights : Multipliers n,
      (finishPhase s j weights observed).val = some (ratio, nextWeights) ∧
      (1 - s.η) / (1 + s.η) ≤ ratio / R ∧
      ratio / R ≤ (1 + s.η) / (1 - s.η) ∧
      (j + 1 < s.L → ∀ index,
        nextIdeal index / 4 ≤ nextWeights index ∧
        nextWeights index ≤ 4 * nextIdeal index) := by
  obtain ⟨pZero, pDefect, hN, hpZero, hR, hz, hu, hd⟩ := hobs
  have hηlt : s.η < 1 := by linarith
  have hNq : (0 : ℚ) < s.observations := by exact_mod_cast hN
  have hNz : (s.observations : ℚ) ≠ 0 := hNq.ne'
  obtain ⟨_, hzeroPos, hl, hh⟩ := relative_quotient_bounds s.η
    (pZero * R) pZero
    (observed.numeratorSum / (s.observations : ℚ))
    ((observed.counts .transversal : ℚ) / (s.observations : ℚ))
    hη hηlt (mul_pos hpZero hR) hpZero hu hz
  have hzero : 0 < observed.counts .transversal := by
    have h := (div_pos_iff_of_pos_right hNq).mp hzeroPos
    exact_mod_cast h
  have hdefect : ∀ index : DefectIndex n,
      0 < observed.counts (.defect index.emptyPair index.fullPair) := by
    intro index
    have hmean := (hd index).2.1
    have he := (hd index).2.2.2.2
    have hpos : 0 < (observed.counts (.defect index.emptyPair index.fullPair) : ℚ) /
        (s.observations : ℚ) :=
      (mul_pos (by linarith : 0 < 1 - s.η) hmean).trans_le he.1
    have h := (div_pos_iff_of_pos_right hNq).mp hpos
    exact_mod_cast h
  let ratio := observed.numeratorSum / (observed.counts .transversal : ℚ)
  let nextWeights := empiricalWeights s j weights observed
  refine ⟨ratio, nextWeights,
    finishPhase_empirical_update s j weights observed hN hzero hdefect, ?_, ?_, ?_⟩
  · have he : (observed.numeratorSum / (s.observations : ℚ)) /
        ((observed.counts .transversal : ℚ) / (s.observations : ℚ)) = ratio := by
      dsimp [ratio]
      field_simp
    simpa only [he, mul_div_cancel_left₀ R hpZero.ne'] using hl
  · have he : (observed.numeratorSum / (s.observations : ℚ)) /
        ((observed.counts .transversal : ℚ) / (s.observations : ℚ)) = ratio := by
      dsimp [ratio]
      field_simp
    simpa only [he, mul_div_cancel_left₀ R hpZero.ne'] using hh
  · intro hj index
    obtain ⟨hw, hpi, hideal, hdrift, he⟩ := hd index
    have hb := learned_multiplier_bounds s.η (weights index) pZero (pDefect index)
      ((observed.counts .transversal : ℚ) / (s.observations : ℚ))
      ((observed.counts (.defect index.emptyPair index.fullPair) : ℚ) /
        (s.observations : ℚ)) (ideal index) (nextIdeal index)
      hη hηsmall hw hpZero hpi hz he hideal hdrift
    have hformula : nextWeights index = weights index *
        ((observed.counts .transversal : ℚ) / (s.observations : ℚ)) /
        ((observed.counts (.defect index.emptyPair index.fullPair) : ℚ) /
          (s.observations : ℚ)) := by
      dsimp [nextWeights, empiricalWeights]
      rw [if_pos hj]
      field_simp
    rwa [← hformula] at hb
