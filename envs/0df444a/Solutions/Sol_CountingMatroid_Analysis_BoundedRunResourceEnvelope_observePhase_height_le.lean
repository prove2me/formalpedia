-- Prove2me | solution 1 for CountingMatroid.Analysis.BoundedRunResourceEnvelope.observePhase_height_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T13:04:41.89577+00:00
-- url     : https://prove2.me/submissions/bef8cb94-e294-4880-baa3-3b66fae5bc2a

import Definitions.Def_CountingMatroidSupport_Computation_Charged
import Definitions.Def_CountingMatroidSupport_Computation_Charged_Extension1
import Definitions.Def_CountingMatroidSupport_Computation_Charged_Extension2
import Definitions.Def_CountingMatroidSupport_Computation_Cost
import Definitions.Def_CountingMatroidSupport_Computation_Dict
import Definitions.Def_CountingMatroidSupport_Computation_Heap
import Definitions.Def_CountingMatroidSupport_Computation_Machine
import Definitions.Def_CountingMatroidSupport_Computation_Num
import Definitions.Def_CountingMatroidSupport_Computation_Queue
import Definitions.Def_CountingMatroidSupport_Computation_Rand
import Definitions.Def_CountingMatroidSupport_Computation_Roster
import Definitions.Def_CountingMatroidSupport_Computation_Slot
import Definitions.Def_CountingMatroidSupport_Computation_Space
import Definitions.Def_CountingMatroidSupport_Computation_Std
import Definitions.Def_CountingMatroid_Analysis_EstimateMedianResource
import Definitions.Def_CountingMatroid_Analysis_RationalHeight
import Definitions.Def_CountingMatroid_Analysis_ScheduleOpeningCost
import Definitions.Def_CountingMatroid_Analysis_ScheduleThermalSetupCost
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
import Theorems.Thm_CountingMatroid_Analysis_BoundedRunResourceEnvelope_observePhase_counts_le
import Theorems.Thm_CountingMatroid_Analysis_BoundedRunResourceEnvelope_recordObservation_height_le

namespace CountingMatroid.Analysis.BoundedRunResourceEnvelope
end CountingMatroid.Analysis.BoundedRunResourceEnvelope
namespace CountingMatroid.Analysis.ScheduleOtherStepsEnvelope
end CountingMatroid.Analysis.ScheduleOtherStepsEnvelope
namespace CountingMatroid.Analysis.LeastHalvingsCost
end CountingMatroid.Analysis.LeastHalvingsCost
namespace CountingMatroid.Analysis
end CountingMatroid.Analysis
namespace CountingMatroid.Meta
end CountingMatroid.Meta
namespace Arlib
end Arlib
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
set_option autoImplicit false

namespace CountingMatroid.Analysis.BoundedRunResourceEnvelope
end CountingMatroid.Analysis.BoundedRunResourceEnvelope
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.BoundedRunResourceEnvelope

open CountingMatroid.Model
open CountingMatroid.Model.Operations
open CountingMatroid.Model.Subroutines
open CountingMatroid.Analysis.RationalHeight

/-- INTERNAL: The observation accumulator has linear height growth in the loop cap.
TEXLINE: main.tex:1362-1378 -/
theorem solution {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (tape : ℕ → Bool)
    (s : AnnealingSchedule) (q : ℚ) (weights : Multipliers n)
    (start : PairedSet n × ℕ)
    (next : CountingMatroid.Program.ObservationCursor n)
    (h : (CountingMatroid.Program.observePhase r o₁ o₂ tape s q weights start).val =
      some next) : rationalHeight next.numeratorSum ≤
      1 + s.observations * (binaryRatLength 1 + n * binaryRatLength s.ρ + 1) := by
  let K := binaryRatLength 1 + n * binaryRatLength s.ρ + 1
  let P : Option (CountingMatroid.Program.ObservationCursor n) → ℕ → Prop :=
    fun acc k => ∀ next, acc = some next → rationalHeight next.numeratorSum ≤ 1 + k * K
  let f : Option (CountingMatroid.Program.ObservationCursor n) → ℕ →
      Arlib.Computation.Charged Op Cell
        (Option (CountingMatroid.Program.ObservationCursor n)) :=
    fun acc index =>
      match acc with
      | none => pure none
      | some current => do
          let onStart ← natEqual index 0
          if onStart then CountingMatroid.Program.recordObservation r o₁ o₂ s.ρ current
          else do
            let next ← CountingMatroid.Program.chainStep r o₁ o₂ tape s.drawTrials q
              weights current.state current.bitCursor
            match next with
            | none => pure none
            | some (state, bitCursor) =>
                CountingMatroid.Program.recordObservation r o₁ o₂ s.ρ
                  ⟨state, bitCursor, current.counts, current.numeratorSum⟩
  have hstep : ∀ acc index k, P acc k → P (f acc index).val (k + 1) := by
    intro acc index k hacc next hnext
    cases acc with
    | none => simp [f] at hnext
    | some current =>
        dsimp [f] at hnext
        by_cases hon : (natEqual index 0).val = true
        · simp only [hon, ite_true] at hnext
          have hcur := hacc current rfl
          have hg := recordObservation_height_le r o₁ o₂ s.ρ current next hnext
          dsimp [K] at *
          nlinarith
        · simp only [Bool.not_eq_true] at hon
          simp only [hon, Bool.false_eq_true, ↓reduceIte,
            Arlib.Computation.Charged.val_bind] at hnext
          split at hnext
          · simp at hnext
          · have hcur := hacc current rfl
            have hg := recordObservation_height_le r o₁ o₂ s.ρ _ next hnext
            dsimp [K, P] at *
            nlinarith
  unfold CountingMatroid.Program.observePhase at h
  simp only [Arlib.Computation.Charged.val_bind] at h
  unfold Arlib.Computation.Charged.repeatFor at h
  have hinit : P (some ⟨start.1, start.2, (allocateCounts n).val, 0⟩) 0 := by
    intro initial hin
    cases Option.some.inj hin
    norm_num [rationalHeight, Nat.log2_eq_log_two]
  have hfinal := chargedFold_count_growth P f hstep
    (List.range s.observations) _ 0 hinit
  simpa using hfinal next h
