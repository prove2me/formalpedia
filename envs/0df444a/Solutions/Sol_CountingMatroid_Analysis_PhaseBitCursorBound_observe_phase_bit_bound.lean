-- Prove2me | solution 1 for CountingMatroid.Analysis.PhaseBitCursorBound.observe_phase_bit_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T16:14:35.411992+00:00
-- url     : https://prove2.me/submissions/57508a7f-9955-4b9f-8651-e182e7f307c7

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
import Definitions.Def_CountingMatroid_Analysis_ChainDrawSiteReplay
import Definitions.Def_CountingMatroid_Analysis_ChainStepIntervalReplay
import Definitions.Def_CountingMatroid_Analysis_EstimateMedianResource
import Definitions.Def_CountingMatroid_Analysis_FirstPhaseFailure
import Definitions.Def_CountingMatroid_Analysis_PhaseChainWork
import Definitions.Def_CountingMatroid_Analysis_PhaseResourcePrimitives
import Definitions.Def_CountingMatroid_Analysis_RationalHeight
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
import Theorems.Thm_CountingMatroid_Analysis_ChainStepBitBound_chain_step_bit_bound
import Theorems.Thm_CountingMatroid_Analysis_PhaseBitCursorBound_traceReturn_preserves_bit_budget

namespace CountingMatroid.Analysis.PhaseBitCursorBound
end CountingMatroid.Analysis.PhaseBitCursorBound
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
namespace CountingMatroid.Analysis.PhaseHistoryMultiplierLength
end CountingMatroid.Analysis.PhaseHistoryMultiplierLength
namespace CountingMatroid.Analysis.FinishPhaseWeightsSize
end CountingMatroid.Analysis.FinishPhaseWeightsSize
namespace CountingMatroid.Analysis.ScheduleOtherStepsEnvelope
end CountingMatroid.Analysis.ScheduleOtherStepsEnvelope
namespace CountingMatroid.Analysis.LeastHalvingsCost
end CountingMatroid.Analysis.LeastHalvingsCost
namespace CountingMatroid.Analysis
end CountingMatroid.Analysis
namespace CountingMatroid.Analysis.ChainStepBitBound
end CountingMatroid.Analysis.ChainStepBitBound
section


set_option autoImplicit false

namespace CountingMatroid.Analysis.BoundedRunResourceEnvelope

open CountingMatroid.Model
open CountingMatroid.Model.Operations
open CountingMatroid.Model.Subroutines
open CountingMatroid.Analysis.RationalHeight





/-- INTERNAL: A charged finite loop preserves a counter bound that grows by one
per iteration. -/
theorem chargedFold_count_growth {ι β : Type} (P : β → ℕ → Prop)
    (f : β → ι → Arlib.Computation.Charged Op Cell β)
    (hf : ∀ b i k, P b k → P (f b i).val (k + 1))
    (l : List ι) (b : β) (k : ℕ) (hb : P b k) :
    P (Arlib.Computation.Charged.foldl f l b).val (k + l.length) := by
  induction l generalizing b k with
  | nil => simpa using hb
  | cons i xs ih =>
      rw [Arlib.Computation.Charged.val_foldl_cons]
      simpa [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        ih (f b i).val (k + 1) (hf b i k hb)



















end CountingMatroid.Analysis.BoundedRunResourceEnvelope

end

section


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace CountingMatroid.Analysis.PhaseBitCursorBound

open CountingMatroid.Model CountingMatroid.Model.Operations CountingMatroid.Program
open CountingMatroid.Analysis.ChainStepBitBound
open CountingMatroid.Analysis.BoundedRunResourceEnvelope









/-- INTERNAL: Recording an observation consumes no fair bits. -/
private theorem record_cursor {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (rho : ℚ) (current next : ObservationCursor n)
    (h : (recordObservation r o₁ o₂ rho current).val = some next) :
    next.bitCursor = current.bitCursor := by
  unfold recordObservation at h
  simp only [Arlib.Computation.Charged.val_bind] at h
  split at h
  · cases h
  · exact (congrArg ObservationCursor.bitCursor (Option.some.inj h)).symm
  · simp only [Arlib.Computation.Charged.val_bind] at h
    exact (congrArg ObservationCursor.bitCursor (Option.some.inj h)).symm





end CountingMatroid.Analysis.PhaseBitCursorBound

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* this round · proved · completed actual-history cursor induction after rejected handoff; both deterministic finishing branches copy the observation cursor. Standalone source elaboration passed.

* this round · proved the global attempt-token invariant for trace returns, restart budget, and observation budget; attempted actual-history induction through zero, abort, and successful predecessor branches. The successful phase cursor composition remains open for the live OPEN handoff.
-/

end
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace CountingMatroid.Analysis.PhaseBitCursorBound
end CountingMatroid.Analysis.PhaseBitCursorBound
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.PhaseBitCursorBound

open CountingMatroid.Model CountingMatroid.Model.Operations CountingMatroid.Program
open CountingMatroid.Analysis.ChainStepBitBound
open CountingMatroid.Analysis.BoundedRunResourceEnvelope

/-- INTERNAL: Each iteration of the actual observation prefix consumes at
most one bounded chain attempt; the initial record consumes none.
TEXLINE: main.tex:1177-1187,1392-1421 -/
theorem solution {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (tape : ℕ → Bool)
    (s : AnnealingSchedule) (q : ℚ) (weights : Multipliers n)
    (start : PairedSet n × ℕ) (K : ℕ)
    (hq : binaryRatLength 1 + n * binaryRatLength q ≤ K)
    (hw : ∀ i, binaryRatLength (weights i) ≤ K)
    (out : ObservationCursor n)
    (h : (observePhase r o₁ o₂ tape s q weights start).val = some out) :
    out.bitCursor ≤ start.2 + s.observations * (1 + 3 * s.drawTrials * (4 * K + n + 1)) := by
  let C := 1 + 3 * s.drawTrials * (4 * K + n + 1)
  let P : Option (ObservationCursor n) → ℕ → Prop :=
    fun acc k => ∀ cur, acc = some cur → cur.bitCursor ≤ start.2 + k * C
  let step : Option (ObservationCursor n) → ℕ →
      Arlib.Computation.Charged Op Cell (Option (ObservationCursor n)) := fun acc index => do
    match acc with
    | none => pure none
    | some current =>
        let onStart ← natEqual index 0
        if onStart then recordObservation r o₁ o₂ s.ρ current
        else
          let next ← chainStep r o₁ o₂ tape s.drawTrials q weights current.state current.bitCursor
          match next with
          | none => pure none
          | some (state, bitCursor) =>
              recordObservation r o₁ o₂ s.ρ ⟨state, bitCursor, current.counts, current.numeratorSum⟩
  have hs : ∀ acc index k, P acc k → P (step acc index).val (k + 1) := by
    intro acc index k hp next hn
    cases acc with
    | none => cases hn
    | some current =>
        dsimp only [step] at hn
        simp only [Arlib.Computation.Charged.val_bind] at hn
        have hc := hp current rfl
        split at hn
        · have he := record_cursor r o₁ o₂ s.ρ current next hn
          dsimp only [C] at hc ⊢
          rw [he, Nat.add_mul, Nat.one_mul]
          omega
        · simp only [Arlib.Computation.Charged.val_bind] at hn
          cases he : (chainStep r o₁ o₂ tape s.drawTrials q weights current.state current.bitCursor).val with
          | none => simp only [he, Arlib.Computation.Charged.val_pure] at hn; cases hn
          | some attempted =>
              cases attempted with
              | mk state stop =>
                  simp only [he] at hn
                  have heq := record_cursor r o₁ o₂ s.ρ _ next hn
                  have hb := chain_step_bit_bound r o₁ o₂ tape s.drawTrials q weights
                    current.state current.bitCursor K hq hw (state, stop) he
                  dsimp only [C] at hc ⊢
                  rw [heq, Nat.add_mul, Nat.one_mul]
                  dsimp only at hb ⊢
                  omega
  let initial : ObservationCursor n := ⟨start.1, start.2, (allocateCounts n).val, 0⟩
  have hf := chargedFold_count_growth P step hs (List.range s.observations)
    (some initial) 0 (by intro cur he; cases Option.some.inj he; simp [initial])
  change (Arlib.Computation.Charged.foldl step (List.range s.observations) (some initial)).val = some out at h
  simpa only [List.length_range, Nat.zero_add] using hf out h
