-- Prove2me | solution 1 for CountingMatroid.Analysis.SinglePhaseIntervalReplay.single_phase_interval_replay
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T16:20:32.024974+00:00
-- url     : https://prove2.me/submissions/026d681d-db78-4f36-ab1d-6d66a8fce276

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
import Definitions.Def_CountingMatroid_Analysis_BoundedUniformReplay
import Definitions.Def_CountingMatroid_Analysis_ChainStepIntervalReplay
import Definitions.Def_CountingMatroid_Analysis_FirstPhaseFailure
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
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.List.Basic
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
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Ring.RingNF
import Theorems.Thm_CountingMatroid_Analysis_ObservePhaseIntervalReplay_observePhase_success_interval
import Theorems.Thm_CountingMatroid_Analysis_RestartPhaseIntervalReplay_restartPhase_success_interval

namespace CountingMatroid.Analysis.SinglePhaseIntervalReplay
end CountingMatroid.Analysis.SinglePhaseIntervalReplay
namespace CountingMatroid.Analysis.RestartPhaseIntervalReplay
end CountingMatroid.Analysis.RestartPhaseIntervalReplay
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
namespace CountingMatroid.Analysis.TraceReturnIntervalReplay
end CountingMatroid.Analysis.TraceReturnIntervalReplay
namespace CountingMatroid.Analysis.ObservePhaseIntervalReplay
end CountingMatroid.Analysis.ObservePhaseIntervalReplay
set_option autoImplicit false

/-!
The actual bounded-run phase composes restart and observation replay with its
deterministic finalization. The proof is uniform in an arbitrary schedule.
-/

namespace CountingMatroid.Analysis.SinglePhaseIntervalReplay
end CountingMatroid.Analysis.SinglePhaseIntervalReplay
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.SinglePhaseIntervalReplay
open CountingMatroid.Model

/-- INTERNAL: Compose restart and observation interval replay through the
actual deterministic finish, product, and table-write suffix of a phase.
TEXLINE: main.tex:1163-1201,1392-1421 -/
theorem solution {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (s : AnnealingSchedule) :
    ∀ a (tape : ℕ → Bool) (previous next : CountingMatroid.Program.AnnealingCursor n),
      (BoundedRunPhase.boundedRunPhase r o₁ o₂ tape s a (some previous)).val = some next →
      previous.bitCursor ≤ next.bitCursor ∧
        ∀ other : ℕ → Bool,
          (∀ i, previous.bitCursor ≤ i → i < next.bitCursor → tape i = other i) →
          (BoundedRunPhase.boundedRunPhase r o₁ o₂ other s a (some previous)).val = some next := by
  intro a tape previous next hrun
  unfold BoundedRunPhase.boundedRunPhase at hrun
  simp only [Arlib.Computation.Charged.val_bind] at hrun
  cases hstarted : (CountingMatroid.Program.restartPhase r o₁ o₂ tape
      s previous.tables a
      previous.bitCursor).val with
  | none =>
      simp only [hstarted, Arlib.Computation.Charged.val_pure] at hrun
      contradiction
  | some started =>
      simp only [hstarted, Arlib.Computation.Charged.val_bind] at hrun
      cases hobserved : (CountingMatroid.Program.observePhase r o₁ o₂ tape
          s
          (CountingMatroid.Program.ratPower
            s.ρ a).val
          previous.currentWeights started).val with
      | none =>
          simp only [hobserved, Arlib.Computation.Charged.val_pure] at hrun
          contradiction
      | some observed =>
          simp only [hobserved, Arlib.Computation.Charged.val_bind] at hrun
          have hcursor : next.bitCursor = observed.bitCursor := by
            cases hfinished : (CountingMatroid.Program.finishPhase
                s a
                previous.currentWeights observed).val with
            | none =>
                simp only [hfinished, Arlib.Computation.Charged.val_pure] at hrun
                contradiction
            | some result =>
                cases result with
                | mk ratio weights =>
                  simp only [hfinished, Arlib.Computation.Charged.val_bind] at hrun
                  by_cases hupdate : (CountingMatroid.Model.Operations.lessThan
                      (CountingMatroid.Model.Operations.successor a).val
                      s.L).val = true
                  · rw [if_pos hupdate] at hrun
                    simp only [Arlib.Computation.Charged.val_bind] at hrun
                    exact (congrArg CountingMatroid.Program.AnnealingCursor.bitCursor
                      (Option.some.inj hrun)).symm
                  · rw [if_neg hupdate] at hrun
                    exact (congrArg CountingMatroid.Program.AnnealingCursor.bitCursor
                      (Option.some.inj hrun)).symm
          have hrestart := RestartPhaseIntervalReplay.restartPhase_success_interval
            r o₁ o₂ s
            previous.tables a previous.bitCursor tape started hstarted
          have hobservation := ObservePhaseIntervalReplay.observePhase_success_interval
            r o₁ o₂ s
            (CountingMatroid.Program.ratPower
              s.ρ a).val
            previous.currentWeights started tape observed hobserved
          refine ⟨hrestart.1.trans (hobservation.1.trans hcursor.symm.le), ?_⟩
          intro other hagree
          have hs := hrestart.2 other (fun i hlo hhi => hagree i hlo
            (hhi.trans_le (hobservation.1.trans hcursor.symm.le)))
          have ho := hobservation.2 other (fun i hlo hhi => hagree i
            (hrestart.1.trans hlo) (hhi.trans_le hcursor.symm.le))
          dsimp only at hs ho
          unfold BoundedRunPhase.boundedRunPhase
          simp only [Arlib.Computation.Charged.val_bind, hs, ho]
          exact hrun
