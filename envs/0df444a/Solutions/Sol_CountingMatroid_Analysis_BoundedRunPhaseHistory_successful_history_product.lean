-- Prove2me | solution 1 for CountingMatroid.Analysis.BoundedRunPhaseHistory.successful_history_product
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T15:45:41.756651+00:00
-- url     : https://prove2.me/submissions/36bcded9-f31d-4e75-acc5-52f2e5158c42

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
section


set_option autoImplicit false

/-!
The phase history below is the value of each prefix of the actual bounded-run
fold, including its absorbing aborted state. Successful local ratio steps
give the product witness used by the lower-tail proof. This is a
deterministic operational representation, not a phase probability estimate.
-/

namespace CountingMatroid.Analysis.BoundedRunPhaseHistory

open CountingMatroid.Model CountingMatroid.Model.Operations
open CountingMatroid.Program CountingMatroid.Analysis.BoundedRunPhase





/-- INTERNAL: Split a charged fold at a prefix while retaining its actual value. -/
private theorem val_foldl_append {α β : Type}
    (f : β → α → Arlib.Computation.Charged Op Cell β)
    (xs ys : List α) (b : β) :
    (Arlib.Computation.Charged.foldl f (xs ++ ys) b).val =
      (Arlib.Computation.Charged.foldl f ys
        (Arlib.Computation.Charged.foldl f xs b).val).val := by
  induction xs generalizing b with
  | nil => rfl
  | cons x xs ih =>
      simpa only [List.cons_append, Arlib.Computation.Charged.val_foldl_cons]
        using ih (f b x).val

/-- INTERNAL: Consecutive history entries are related by the actual phase
body, with the previously reached tables, weights, product and bit cursor.
TEXLINE: main.tex:1160-1205 -/
theorem phaseHistory_succ {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (tape : ℕ → Bool) (s : AnnealingSchedule) (j : ℕ) :
    phaseHistory r o₁ o₂ tape s (j + 1) =
      (boundedRunPhase r o₁ o₂ tape s j
        (phaseHistory r o₁ o₂ tape s j)).val := by
  unfold phaseHistory Arlib.Computation.Charged.repeatFor
  rw [List.range_succ, val_foldl_append]
  rfl











end CountingMatroid.Analysis.BoundedRunPhaseHistory

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r18 · proved · represented actual phase-fold prefixes; proved their successor relation and final-output equality, reconstructed an accurate-ratio witness from successful local steps, and covered witness failure by the first failed phase. No probability estimate or unproved declaration introduced.
-/

end
set_option autoImplicit false

/-!
The phase history below is the value of each prefix of the actual bounded-run
fold, including its absorbing aborted state. Successful local ratio steps
give the product witness used by the lower-tail proof. This is a
deterministic operational representation, not a phase probability estimate.
-/

namespace CountingMatroid.Analysis.BoundedRunPhaseHistory
end CountingMatroid.Analysis.BoundedRunPhaseHistory
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.BoundedRunPhaseHistory

open CountingMatroid.Model CountingMatroid.Model.Operations
open CountingMatroid.Program CountingMatroid.Analysis.BoundedRunPhase

/-- INTERNAL: Local successful-ratio steps of the actual bounded phase fold
produce the accurate-ratio witness, including a nonaborted final cursor.
The product invariant is proved by cancellation of consecutive positive
accumulated products, rather than assumed as a property of a transcript.
TEXLINE: main.tex:1273-1304 -/
theorem solution {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (p : InputParams) (tape : ℕ → Bool)
    (hgood : ∀ j < (CountingMatroid.Interface.Pseudocode.setup n p).L,
      PhaseRatioStep r o₁ o₂ p tape j) :
    let s := CountingMatroid.Interface.Pseudocode.setup n p
    let C := fun j => TransversalPartition.partitionSum r o₁ o₂ (s.ρ ^ j)
    ∃ R : ℕ → ℚ,
      (∃ current : AnnealingCursor n,
        phaseHistory r o₁ o₂ tape s s.L = some current ∧
        current.product = ∏ j ∈ Finset.range s.L, R j) ∧
      ∀ j < s.L,
        (1 - s.η) / (1 + s.η) ≤ R j / (C (j + 1) / C j) ∧
        R j / (C (j + 1) / C j) ≤ (1 + s.η) / (1 - s.η) := by
  let s := CountingMatroid.Interface.Pseudocode.setup n p
  let history := phaseHistory r o₁ o₂ tape s
  let P := fun j => (history j).elim (0 : ℚ) (fun current => current.product)
  let R := fun j => P (j + 1) / P j
  have hzero : history 0 = some (initialCursor n s) := rfl
  have hPzero : P 0 = 1 := rfl
  have hnext (j : ℕ) (hj : j < s.L) :
      ∃ current next : AnnealingCursor n,
        history j = some current ∧ history (j + 1) = some next ∧
        0 < current.product ∧ 0 < next.product ∧
        (1 - s.η) / (1 + s.η) ≤
          (next.product / current.product) /
            (TransversalPartition.partitionSum r o₁ o₂ (s.ρ ^ (j + 1)) /
              TransversalPartition.partitionSum r o₁ o₂ (s.ρ ^ j)) ∧
        (next.product / current.product) /
            (TransversalPartition.partitionSum r o₁ o₂ (s.ρ ^ (j + 1)) /
              TransversalPartition.partitionSum r o₁ o₂ (s.ρ ^ j)) ≤
          (1 + s.η) / (1 - s.η) := by
    obtain ⟨current, next, hcurrent, hstep, hpos, hpos', hratio⟩ := hgood j hj
    refine ⟨current, next, hcurrent, ?_, hpos, hpos', hratio⟩
    change phaseHistory r o₁ o₂ tape s (j + 1) = some next
    rw [phaseHistory_succ, hcurrent, hstep]
  have hstates (k : ℕ) (hk : k ≤ s.L) :
      ∃ current : AnnealingCursor n, history k = some current ∧
        0 < current.product := by
    cases k with
    | zero => exact ⟨initialCursor n s, hzero, by norm_num [initialCursor]⟩
    | succ k =>
        obtain ⟨current, next, _, hn, _, hp, _⟩ := hnext k (by omega)
        exact ⟨next, hn, hp⟩
  have hPpos (k : ℕ) (hk : k ≤ s.L) : 0 < P k := by
    obtain ⟨current, hc, hp⟩ := hstates k hk
    simpa only [P, hc, Option.elim_some] using hp
  have hprod (k : ℕ) (hk : k ≤ s.L) :
      (∏ j ∈ Finset.range k, R j) = P k := by
    induction k with
    | zero => simp only [Finset.range_zero, Finset.prod_empty, hPzero]
    | succ k ih =>
        rw [Finset.prod_range_succ, ih (by omega)]
        dsimp only [R]
        field_simp [(hPpos k (by omega)).ne']
  refine ⟨R, ?_, ?_⟩
  · obtain ⟨current, hc, _⟩ := hstates s.L le_rfl
    refine ⟨current, hc, ?_⟩
    have hp := hprod s.L le_rfl
    simpa only [P, hc, Option.elim_some] using hp.symm
  · intro j hj
    obtain ⟨current, next, hc, hn, _, _, hr⟩ := hnext j hj
    simpa only [R, P, hc, hn, Option.elim_some] using hr
