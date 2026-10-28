-- Prove2me | solution 1 for CountingMatroid.Analysis.ChainStepBitBound.boundedUniform_cursor_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T15:06:57.716145+00:00
-- url     : https://prove2.me/submissions/bc03f7f3-a1b2-4a2e-8fc7-8d284a41a778

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
import Definitions.Def_CountingMatroid_Analysis_ChainDrawSiteReplay
import Definitions.Def_CountingMatroid_Analysis_ChainStepIntervalReplay
import Definitions.Def_CountingMatroid_Analysis_EstimateMedianResource
import Definitions.Def_CountingMatroid_Analysis_PhaseChainWork
import Definitions.Def_CountingMatroid_Analysis_PhaseResourcePrimitives
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

namespace CountingMatroid.Analysis.ChainStepBitBound
end CountingMatroid.Analysis.ChainStepBitBound
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
section


set_option autoImplicit false

namespace CountingMatroid.Analysis.ChainStepBitBound

open CountingMatroid.Model CountingMatroid.Model.Operations CountingMatroid.Program
open CountingMatroid.Analysis.ScheduleOtherStepsEnvelope
open CountingMatroid.Analysis.ObservationRoundDrawSites

/-- INTERNAL: Sum a uniform cursor increment along an actual charged fold. -/
private theorem fold_cursor_growth {α β : Type}
    (f : β → α → Arlib.Computation.Charged Op Cell β) (cursor : β → ℕ)
    (D : ℕ) (hf : ∀ b a, cursor (f b a).val ≤ cursor b + D)
    (xs : List α) (b : β) :
    cursor (Arlib.Computation.Charged.foldl f xs b).val ≤ cursor b + xs.length * D := by
  induction xs generalizing b with
  | nil => simp
  | cons a xs ih =>
      rw [Arlib.Computation.Charged.val_foldl_cons]
      have h := ih (f b a).val
      have hs := hf b a
      simp only [List.length_cons, Nat.add_mul, Nat.one_mul]
      omega











end CountingMatroid.Analysis.ChainStepBitBound

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* this round · proved capped-uniform cursor growth and chain/stopped-site three-draw bounds; avoided an ill-typed simplified charged Boolean condition with a local transparency setting.
-/

end
set_option autoImplicit false

namespace CountingMatroid.Analysis.ChainStepBitBound
end CountingMatroid.Analysis.ChainStepBitBound
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.ChainStepBitBound

open CountingMatroid.Model CountingMatroid.Model.Operations CountingMatroid.Program
open CountingMatroid.Analysis.ScheduleOtherStepsEnvelope
open CountingMatroid.Analysis.ObservationRoundDrawSites

/-- INTERNAL: All rejection trials together consume at most their cap times
the exact implementation width, including draws which abort.
TEXLINE: main.tex:1392-1421 -/
theorem solution (tape : ℕ → Bool) (trials v cursor : ℕ) :
    (boundedUniform tape trials v cursor).val.2 ≤
      cursor + trials * ((v - 1).log2 + 1) := by
  let width := (v - 1).log2 + 1
  have htrial (inner : ℕ × ℕ) :
      (Arlib.Computation.Charged.repeatFor (fun _ inner => do
        let bit ← fairBit tape inner.2
        let value ← appendBit inner.1 bit
        let next ← successor inner.2
        pure (value, next)) width inner).val.2 ≤ inner.2 + width := by
    simpa only [Arlib.Computation.Charged.repeatFor, List.length_range,
      Nat.mul_one] using fold_cursor_growth
        (fun inner (_ : ℕ) => do
          let bit ← fairBit tape inner.2
          let value ← appendBit inner.1 bit
          let next ← successor inner.2
          pure (value, next)) Prod.snd 1 (by intro b a; rfl)
        (List.range width) inner
  unfold boundedUniform
  simp only [Arlib.Computation.Charged.val_bind]
  split
  · simp only [Arlib.Computation.Charged.val_pure]; omega
  · simp only [Arlib.Computation.Charged.val_bind]
    split
    · simp only [Arlib.Computation.Charged.val_pure]; omega
    · simp only [Arlib.Computation.Charged.val_bind, Arlib.Computation.Charged.val_pure,
        uniformWidth, Arlib.Computation.Charged.val_op, Arlib.Computation.Charged.repeatFor]
      apply (fold_cursor_growth _ Prod.snd width ?_ _ (none, cursor)).trans_eq
        (by simp only [List.length_range, width, Nat.mul_comm])
      intro acc index
      simp only [Arlib.Computation.Charged.val_bind]
      split
      · simp only [Arlib.Computation.Charged.val_pure]; omega
      · simp only [Arlib.Computation.Charged.val_bind]
        have ht := htrial (0, acc.2)
        split <;> exact ht
