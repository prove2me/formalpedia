-- Prove2me | solution 1 for CountingMatroid.Analysis.RestartReturnAbortAttribution.return_attribution
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T16:34:19.487299+00:00
-- url     : https://prove2.me/submissions/40f2bb18-cdda-49dc-8b95-10afb09c3a55

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
import Definitions.Def_CountingMatroid_Analysis_AnnealingPartitionDrift
import Definitions.Def_CountingMatroid_Analysis_BoundedRunPhase
import Definitions.Def_CountingMatroid_Analysis_BoundedRunPhaseHistory
import Definitions.Def_CountingMatroid_Analysis_BoundedRunPhaseWork
import Definitions.Def_CountingMatroid_Analysis_BoundedUniformAbortMass
import Definitions.Def_CountingMatroid_Analysis_BoundedUniformReplay
import Definitions.Def_CountingMatroid_Analysis_ChainDrawSiteReplay
import Definitions.Def_CountingMatroid_Analysis_ChainStepIntervalReplay
import Definitions.Def_CountingMatroid_Analysis_DefectPartitionPositive
import Definitions.Def_CountingMatroid_Analysis_EmpiricalPhaseCertificate
import Definitions.Def_CountingMatroid_Analysis_EstimateMedianResource
import Definitions.Def_CountingMatroid_Analysis_FinishPhaseEmpiricalUpdate
import Definitions.Def_CountingMatroid_Analysis_FinishPhaseWork
import Definitions.Def_CountingMatroid_Analysis_FirstPhaseFailure
import Definitions.Def_CountingMatroid_Analysis_InitialMultipliersGood
import Definitions.Def_CountingMatroid_Analysis_ObservePhaseWork
import Definitions.Def_CountingMatroid_Analysis_PhaseChainWork
import Definitions.Def_CountingMatroid_Analysis_PhaseMeanCertificate
import Definitions.Def_CountingMatroid_Analysis_PhaseObservationExperiment
import Definitions.Def_CountingMatroid_Analysis_PhaseResourcePrimitives
import Definitions.Def_CountingMatroid_Analysis_RationalHeight
import Definitions.Def_CountingMatroid_Analysis_RelativeObservationBounds
import Definitions.Def_CountingMatroid_Analysis_RestartAttemptAccounting
import Definitions.Def_CountingMatroid_Analysis_RestartDrawProbe
import Definitions.Def_CountingMatroid_Analysis_RestartReturnAbortAttribution
import Definitions.Def_CountingMatroid_Analysis_ScheduleConfidence
import Definitions.Def_CountingMatroid_Analysis_ScheduleOpeningCost
import Definitions.Def_CountingMatroid_Analysis_ScheduleThermalSetupCost
import Definitions.Def_CountingMatroid_Analysis_StationaryMeanIdentities
import Definitions.Def_CountingMatroid_Analysis_TransversalClassPartition
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
import Mathlib.Algebra.Order.Ring.Pow
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
import Mathlib.Data.List.Induction
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
import Theorems.Thm_CountingMatroid_Analysis_RestartReturnAbortAttribution_returnScan_attr

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
namespace CountingMatroid.Analysis.SuccessfulPrefixAbortBound
end CountingMatroid.Analysis.SuccessfulPrefixAbortBound
namespace CountingMatroid.Analysis.BoundedRunResourceEnvelope
end CountingMatroid.Analysis.BoundedRunResourceEnvelope
namespace CountingMatroid.Analysis.BoundedRunOtherSteps
end CountingMatroid.Analysis.BoundedRunOtherSteps
namespace CountingMatroid.Analysis.ScheduleOtherStepsEnvelope
end CountingMatroid.Analysis.ScheduleOtherStepsEnvelope
namespace CountingMatroid.Analysis.LeastHalvingsCost
end CountingMatroid.Analysis.LeastHalvingsCost
namespace CountingMatroid.Analysis
end CountingMatroid.Analysis
namespace CountingMatroid.Analysis.RestartPhaseWork
end CountingMatroid.Analysis.RestartPhaseWork
namespace CountingMatroid.Analysis.BoundedRunPhase
end CountingMatroid.Analysis.BoundedRunPhase
namespace CountingMatroid.Analysis.FinishPhaseWeightsSize
end CountingMatroid.Analysis.FinishPhaseWeightsSize
namespace CountingMatroid.Analysis.BoundedRunOracleCalls
end CountingMatroid.Analysis.BoundedRunOracleCalls
namespace CountingMatroid.Analysis.ResourceBound
end CountingMatroid.Analysis.ResourceBound
namespace CountingMatroid.Analysis.ChainStepNoninvalid
end CountingMatroid.Analysis.ChainStepNoninvalid
namespace CountingMatroid.Analysis.ObservationRoundDrawSites
end CountingMatroid.Analysis.ObservationRoundDrawSites
namespace CountingMatroid.Analysis.ClassifiedStateSelection
end CountingMatroid.Analysis.ClassifiedStateSelection
section


set_option autoImplicit false

/-!
Return-level abort attribution for one capped return scan. A return either
reaches a non-invalid continuing state, exhausts the shared attempt cap, or
aborts at a draw whose descriptor is captured by a concrete sticky probe
with the right ordinal. A probe whose ordinal is at least the return's final
count cannot be disturbed by this return's own processing.
-/
namespace CountingMatroid.Analysis.RestartReturnAbortAttribution

open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.RestartAttemptAccounting
open CountingMatroid.Analysis.RestartDrawProbe
open CountingMatroid.Analysis.ObservationRoundDrawSites



variable {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
  (tape : ℕ → Bool) (s : AnnealingSchedule) (q : ℚ) (w : Multipliers n)















































/-- INTERNAL: `countedReturn`'s public value in terms of `rawScan` over the
actual restart cap. -/
private theorem countedReturn_eq (start : RestartCursor n) (count : ℕ) :
    (countedReturn r o₁ o₂ tape s q w start count).val =
      (let raw := rawScan r o₁ o₂ tape s q w (List.range s.restartCap)
        ((some start, false), count)
       (if raw.1.2 then raw.1.1 else none, raw.2)) := by
  unfold countedReturn rawScan Arlib.Computation.Charged.repeatWhile
  simp only [Arlib.Computation.Charged.val_bind, Arlib.Computation.Charged.val_pure]

/-- INTERNAL: `probedReturn`'s public value in terms of `probedScan` over the
actual restart cap. -/
private theorem probedReturn_eq (ordinal : ℕ) (draw : Fin 3) (start : RestartCursor n)
    (count : ℕ) (observed : Option (ℕ × ℕ)) :
    (probedReturn r o₁ o₂ tape s q w ordinal draw start count observed).val =
      (let probed := probedScan r o₁ o₂ tape s q w ordinal draw (List.range s.restartCap)
        (((some start, false), count), observed)
       ((if probed.1.1.2 then probed.1.1.1 else none, probed.1.2), probed.2)) := by
  unfold probedReturn probedScan Arlib.Computation.Charged.repeatWhile
  simp only [Arlib.Computation.Charged.val_bind, Arlib.Computation.Charged.val_pure]



end CountingMatroid.Analysis.RestartReturnAbortAttribution

end
set_option autoImplicit false

/-!
Return-level abort attribution for one capped return scan. A return either
reaches a non-invalid continuing state, exhausts the shared attempt cap, or
aborts at a draw whose descriptor is captured by a concrete sticky probe
with the right ordinal. A probe whose ordinal is at least the return's final
count cannot be disturbed by this return's own processing.
-/
namespace CountingMatroid.Analysis.RestartReturnAbortAttribution
end CountingMatroid.Analysis.RestartReturnAbortAttribution
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.RestartReturnAbortAttribution

open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.RestartAttemptAccounting
open CountingMatroid.Analysis.RestartDrawProbe
open CountingMatroid.Analysis.ObservationRoundDrawSites



variable {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
  (tape : ℕ → Bool) (s : AnnealingSchedule) (q : ℚ) (w : Multipliers n)

/-- One capped return scan either reaches a non-invalid continuing state,
exhausts the shared restart cap, or aborts at a draw whose descriptor is
captured by the concrete sticky probe at the matching ordinal. A probe at
or beyond the return's final count is never disturbed by this return.
PAPER: main.tex:1163-1176,1392-1421 -/
theorem solution (start : RestartCursor n) (count : ℕ)
    (hvalid : (classifyState start.state).val ≠ .invalid) (hinv : start.attempts = count) :
    count ≤ (countedReturn r o₁ o₂ tape s q w start count).val.2 ∧
    ((∃ final : RestartCursor n,
        (countedReturn r o₁ o₂ tape s q w start count).val.1 = some final ∧
        (classifyState final.state).val ≠ .invalid ∧
        final.attempts = (countedReturn r o₁ o₂ tape s q w start count).val.2 ∧
        ∀ ordinal (draw : Fin 3),
          (countedReturn r o₁ o₂ tape s q w start count).val.2 ≤ ordinal →
          (probedReturn r o₁ o₂ tape s q w ordinal draw start count none).val =
            ((countedReturn r o₁ o₂ tape s q w start count).val, none))
      ∨ (s.restartCap ≤ (countedReturn r o₁ o₂ tape s q w start count).val.2 ∧
          (countedReturn r o₁ o₂ tape s q w start count).val.1 = none)
      ∨ (∃ (ordinal : ℕ) (draw : Fin 3) (d : ℕ × ℕ), count ≤ ordinal ∧ ordinal < s.restartCap ∧
          (countedReturn r o₁ o₂ tape s q w start count).val.1 = none ∧
          (boundedUniform tape s.drawTrials d.2 d.1).val.1 = none ∧
          (probedReturn r o₁ o₂ tape s q w ordinal draw start count none).val.2 = some d)) := by
  obtain ⟨hle, hcases⟩ := returnScan_attr r o₁ o₂ tape s q w (List.range s.restartCap) start
    count hvalid hinv
  rw [countedReturn_eq]
  dsimp only
  rcases hcases with ⟨final, hfinal1, hfinal2, hfinal3, hfinal4, hfinal5⟩
    | ⟨hcapped1, hcapped1b, hcapped2⟩
    | ⟨habort1, habort1b, ordinal, draw, d, hge, hcapord, hfail, hcap⟩
  · by_cases hdone : (rawScan r o₁ o₂ tape s q w (List.range s.restartCap)
        ((some start, false), count)).1.2
    · refine ⟨hle, Or.inl ⟨final, by simp [hdone, hfinal1], hfinal2, by simp [hfinal3], ?_⟩⟩
      intro ordinal draw hord
      rw [probedReturn_eq, hfinal5 ordinal draw (by simpa using hord)]
    · have hlen : (rawScan r o₁ o₂ tape s q w (List.range s.restartCap)
          ((some start, false), count)).2 = count + s.restartCap := by
        rw [hfinal4 hdone, List.length_range]
      exact ⟨hle, Or.inr (Or.inl ⟨by omega, by simp [hdone]⟩)⟩
  · refine ⟨hle, Or.inr (Or.inl ⟨hcapped2, ?_⟩)⟩
    simp [hcapped1b, hcapped1]
  · refine ⟨hle, Or.inr (Or.inr ⟨ordinal, draw, d, hge, hcapord, by simp [habort1b, habort1],
      hfail,
      ?_⟩)⟩
    rw [probedReturn_eq]
    simp [hcap]
