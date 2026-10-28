-- Prove2me | solution 1 for CountingMatroid.Analysis.ObservePhaseIntervalReplay.observePhase_success_interval
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T16:00:41.310797+00:00
-- url     : https://prove2.me/submissions/76dc2ced-3f66-4b51-ae29-e56cf4c5f6ea

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
import Definitions.Def_CountingMatroid_Analysis_BoundedUniformReplay
import Definitions.Def_CountingMatroid_Analysis_ChainStepIntervalReplay
import Definitions.Def_CountingMatroid_Model_Operations
import Definitions.Def_CountingMatroid_Model_Prelude
import Definitions.Def_CountingMatroid_Model_Program
import Definitions.Def_CountingMatroid_Model_Subroutines
import Lean
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Group.Int
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
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Ring.RingNF
import Theorems.Thm_CountingMatroid_Analysis_ChainStepIntervalReplay_chainStep_success_interval
import Theorems.Thm_CountingMatroid_Analysis_ChainStepIntervalReplay_foldl_successReplay

namespace CountingMatroid.Analysis.ObservePhaseIntervalReplay
end CountingMatroid.Analysis.ObservePhaseIntervalReplay
namespace CountingMatroid.Meta
end CountingMatroid.Meta
namespace Arlib
end Arlib
section


set_option autoImplicit false

/-!
Successful observation trajectories have monotone cursors and replay from the
consumed interval. Recording a state reads no tape, while each transition uses
the proved chain-step invariant. An aborted observation remains absorbing.
-/

namespace CountingMatroid.Analysis.ObservePhaseIntervalReplay
open CountingMatroid.Model CountingMatroid.Model.Operations CountingMatroid.Program
open CountingMatroid.Analysis.ChainStepIntervalReplay

/-- INTERNAL: Recording an observation preserves its fair-bit cursor exactly.
TEXLINE: main.tex:1181-1187 -/
private theorem recordObservation_cursor {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (rho : ℚ) (current next : ObservationCursor n)
    (h : (recordObservation r o₁ o₂ rho current).val = some next) :
    next.bitCursor = current.bitCursor := by
  unfold recordObservation at h
  simp only [Arlib.Computation.Charged.val_bind] at h
  split at h
  · cases h
  · simp only [Arlib.Computation.Charged.val_bind] at h
    exact (congrArg ObservationCursor.bitCursor (Option.some.inj h)).symm
  · simp only [Arlib.Computation.Charged.val_bind] at h
    exact (congrArg ObservationCursor.bitCursor (Option.some.inj h)).symm



end CountingMatroid.Analysis.ObservePhaseIntervalReplay

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r21 · proved · observation-loop interval replay, using exact cursor
  preservation by recording and successful chain-step replay.
-/

end
set_option autoImplicit false

/-!
Successful observation trajectories have monotone cursors and replay from the
consumed interval. Recording a state reads no tape, while each transition uses
the proved chain-step invariant. An aborted observation remains absorbing.
-/

namespace CountingMatroid.Analysis.ObservePhaseIntervalReplay
end CountingMatroid.Analysis.ObservePhaseIntervalReplay
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.ObservePhaseIntervalReplay
open CountingMatroid.Model CountingMatroid.Model.Operations CountingMatroid.Program
open CountingMatroid.Analysis.ChainStepIntervalReplay

/-- INTERNAL: Replay a successful correlated-observation loop from the interval
it consumed, retaining every state count and its numerator sum.
TEXLINE: main.tex:1181-1187,1392-1421 -/
theorem solution {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (s : AnnealingSchedule) (q : ℚ)
    (weights : Multipliers n) (start : PairedSet n × ℕ) :
    SuccessReplay (fun tape => (observePhase r o₁ o₂ tape s q weights start).val)
      ObservationCursor.bitCursor start.2 := by
  unfold observePhase
  simp only [Arlib.Computation.Charged.val_bind, Arlib.Computation.Charged.repeatFor]
  apply foldl_successReplay
  · intro tape a
    rfl
  · intro current index tape next hrun
    simp only [Arlib.Computation.Charged.val_bind] at hrun
    by_cases hstart : (natEqual index 0).val = true
    · rw [if_pos hstart] at hrun
      have hcursor := recordObservation_cursor r o₁ o₂ s.ρ current next hrun
      refine ⟨hcursor.symm.le, ?_⟩
      intro other _
      simp only [Arlib.Computation.Charged.val_bind]
      rw [if_pos hstart]
      exact hrun
    · rw [if_neg hstart] at hrun
      simp only [Arlib.Computation.Charged.val_bind] at hrun
      cases hchain : (chainStep r o₁ o₂ tape s.drawTrials q weights
          current.state current.bitCursor).val with
      | none =>
          simp only [hchain, Arlib.Computation.Charged.val_pure] at hrun
          contradiction
      | some step =>
          simp only [hchain] at hrun
          have hcursor := recordObservation_cursor r o₁ o₂ s.ρ
            ⟨step.1, step.2, current.counts, current.numeratorSum⟩ next hrun
          have hlocal := chainStep_success_interval r o₁ o₂ s.drawTrials q weights
            current.state current.bitCursor tape step hchain
          refine ⟨hlocal.1.trans hcursor.symm.le, ?_⟩
          intro other hagree
          have heq := hlocal.2 other (by simpa only [hcursor] using hagree)
          simp only [Arlib.Computation.Charged.val_bind]
          rw [if_neg hstart]
          simp only [Arlib.Computation.Charged.val_bind]
          dsimp only at heq
          rw [heq]
          cases step
          exact hrun
