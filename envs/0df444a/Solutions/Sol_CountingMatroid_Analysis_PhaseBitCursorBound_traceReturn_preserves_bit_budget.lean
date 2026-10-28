-- Prove2me | solution 1 for CountingMatroid.Analysis.PhaseBitCursorBound.traceReturn_preserves_bit_budget
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T15:58:31.604871+00:00
-- url     : https://prove2.me/submissions/800d375a-f3ce-4528-b42e-00306cd546ed

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
set_option backward.isDefEq.respectTransparency false

namespace CountingMatroid.Analysis.PhaseBitCursorBound

open CountingMatroid.Model CountingMatroid.Model.Operations CountingMatroid.Program
open CountingMatroid.Analysis.ChainStepBitBound
open CountingMatroid.Analysis.BoundedRunResourceEnvelope

/-- INTERNAL: Preserve an invariant across a charged loop with early breaks. -/
private theorem foldWhile_preserves {α β : Type} (P : β → Prop)
    (f : β → α → Arlib.Computation.Charged Op Cell (Option β))
    (hf : ∀ b a next, P b → (f b a).val = some next → P next)
    (xs : List α) (b : β) (hb : P b) :
    P (Arlib.Computation.Charged.foldlWhile f xs b).val := by
  induction xs generalizing b with
  | nil => exact hb
  | cons a xs ih =>
      cases he : (f b a).val with
      | none =>
          simp only [Arlib.Computation.Charged.val] at he ⊢
          simpa only [Arlib.Computation.Charged.foldlWhile, he] using hb
      | some next =>
          have hn := ih next (hf b a next hb he)
          simp only [Arlib.Computation.Charged.val] at he hn ⊢
          simpa only [Arlib.Computation.Charged.foldlWhile, he] using hn













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

/-- INTERNAL: The global restart-attempt counter pays for every underlying
chain step, across positive-time trace returns; the guard enforces the cap.
TEXLINE: main.tex:1163-1176,1392-1421 -/
theorem solution {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (tape : ℕ → Bool)
    (s : AnnealingSchedule) (q : ℚ) (weights : Multipliers n)
    (base K : ℕ) (start out : RestartCursor n)
    (hq : binaryRatLength 1 + n * binaryRatLength q ≤ K)
    (hw : ∀ i, binaryRatLength (weights i) ≤ K)
    (ha : start.attempts ≤ s.restartCap)
    (hb : start.bitCursor ≤ base + start.attempts * (1 + 3 * s.drawTrials * (4 * K + n + 1)))
    (h : (traceReturn r o₁ o₂ tape s q weights start).val = some out) :
    out.attempts ≤ s.restartCap ∧
    out.bitCursor ≤ base + out.attempts * (1 + 3 * s.drawTrials * (4 * K + n + 1)) := by
  let C := 1 + 3 * s.drawTrials * (4 * K + n + 1)
  let P : Option (RestartCursor n) → Prop := fun acc =>
    ∀ cur, acc = some cur → cur.attempts ≤ s.restartCap ∧
      cur.bitCursor ≤ base + cur.attempts * C
  let step : (Option (RestartCursor n) × Bool) → ℕ →
      Arlib.Computation.Charged Op Cell (Option (Option (RestartCursor n) × Bool)) :=
    fun acc _ => do
      if acc.2 then pure none
      else match acc.1 with
      | none => pure none
      | some current =>
          let allowed ← lessThan current.attempts s.restartCap
          if allowed then
            let attempted ← chainStep r o₁ o₂ tape s.drawTrials q weights current.state current.bitCursor
            let attempts ← successor current.attempts
            match attempted with
            | none => pure (some (none, true))
            | some (state, bitCursor) =>
                let kind ← classifyState state
                let returned ← match kind with
                  | .transversal => pure true
                  | _ => pure false
                pure (some (some ⟨state, bitCursor, attempts⟩, returned))
          else pure (some (none, true))
  have hs : ∀ acc index next, P acc.1 → (step acc index).val = some next → P next.1 := by
    intro acc index next hp he cur hc
    dsimp only [step] at he
    split at he
    · cases he
    · cases ha' : acc.1 with
      | none => simp only [ha', Arlib.Computation.Charged.val_pure] at he; cases he
      | some current =>
          simp only [ha', Arlib.Computation.Charged.val_bind, lessThan,
            Arlib.Computation.Charged.val_op] at he
          split at he
          · rename_i hallowed
            have hlt : current.attempts < s.restartCap := of_decide_eq_true hallowed
            simp only [Arlib.Computation.Charged.val_bind] at he
            cases hchain : (chainStep r o₁ o₂ tape s.drawTrials q weights
                current.state current.bitCursor).val with
            | none =>
                simp only [hchain, Arlib.Computation.Charged.val_pure, Option.some.injEq] at he
                subst next
                cases hc
            | some attempted =>
                simp only [hchain, Arlib.Computation.Charged.val_bind, successor,
                  Arlib.Computation.Charged.val_op] at he
                have hbit := chain_step_bit_bound r o₁ o₂ tape s.drawTrials q weights
                  current.state current.bitCursor K hq hw attempted hchain
                have hcur := (hp current ha').2
                cases attempted with
                | mk state stop =>
                    cases hk : (classifyState state).val <;>
                      simp only [hk, Arlib.Computation.Charged.val_bind,
                        Arlib.Computation.Charged.val_pure, Option.some.injEq] at he <;>
                      subst next <;> cases Option.some.inj hc <;>
                      exact ⟨by dsimp only; omega, by
                        dsimp only [C, RestartCursor.bitCursor, RestartCursor.attempts] at hcur ⊢
                        rw [Nat.add_mul, Nat.one_mul]
                        omega⟩
          · simp only [Arlib.Computation.Charged.val_pure, Option.some.injEq] at he
            subst next
            cases hc
  have hscan := foldWhile_preserves (fun acc => P acc.1) step hs
    (List.range s.restartCap) (some start, false)
    (by intro cur he; cases Option.some.inj he; exact ⟨ha, hb⟩)
  unfold traceReturn at h
  simp only [Arlib.Computation.Charged.val_bind, Arlib.Computation.Charged.repeatWhile] at h
  change (if (Arlib.Computation.Charged.foldlWhile step (List.range s.restartCap)
      (some start, false)).val.2 then
    pure (Arlib.Computation.Charged.foldlWhile step (List.range s.restartCap)
      (some start, false)).val.1 else pure none :
    Arlib.Computation.Charged Op Cell (Option (RestartCursor n))).val = some out at h
  split at h
  · exact hscan out h
  · cases h
