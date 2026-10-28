-- Prove2me | solution 1 for CountingMatroid.Analysis.RestartPhaseWork.restartPhase_otherSteps_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T16:05:19.758782+00:00
-- url     : https://prove2.me/submissions/f2fc4f99-1694-4df4-b839-c8640ea52d65

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
import Theorems.Thm_CountingMatroid_Analysis_BoundedRunResourceEnvelope_ratPower_binary_length_le
import Theorems.Thm_CountingMatroid_Analysis_BoundedRunResourceEnvelope_ratPower_fold_otherSteps_le
import Theorems.Thm_CountingMatroid_Analysis_RestartPhaseWork_traceReturn_otherSteps_le

namespace CountingMatroid.Analysis.ResourceBound
end CountingMatroid.Analysis.ResourceBound
namespace CountingMatroid.Analysis.BoundedRunResourceEnvelope
end CountingMatroid.Analysis.BoundedRunResourceEnvelope
namespace CountingMatroid.Analysis.RestartPhaseWork
end CountingMatroid.Analysis.RestartPhaseWork
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


/-!
# Resource bounds for the charged rational median

The insertion scan preserves sorted values and has polynomial charged cost
when its input rational encodings have a common bound.
-/

set_option autoImplicit false

namespace CountingMatroid.Analysis.ResourceBound

open CountingMatroid.Model
open CountingMatroid.Model.Subroutines
open CountingMatroid.Model.Operations





/-- INTERNAL: A bound on each member of a charged list scan bounds its total
nonoracle charge. -/
theorem otherSteps_foldl_le_of_mem {β ι : Type}
    (f : β → ι → Arlib.Computation.Charged Op Cell β)
    (l : List ι) (k : ℕ)
    (h : ∀ b a, a ∈ l → otherSteps (f b a) ≤ k) (b : β) :
    otherSteps (Arlib.Computation.Charged.foldl f l b) ≤ l.length * k := by
  induction l generalizing b with
  | nil => simp [otherSteps]
  | cons a as ih =>
      rw [show Arlib.Computation.Charged.foldl f (a :: as) b =
        f b a >>= fun b' => Arlib.Computation.Charged.foldl f as b' from rfl,
        otherSteps_bind]
      have hfirst := h b a (by simp)
      have htail := ih (fun b' a' ha' => h b' a' (by simp [ha'])) (f b a).val
      simpa [List.length_cons, Nat.succ_mul, Nat.add_comm, Nat.add_left_comm,
        Nat.add_assoc] using Nat.add_le_add hfirst htail













end CountingMatroid.Analysis.ResourceBound

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r8 · proved · extracted and closed the median length, sign, and charge invariants used by the estimator.
-/

end

section


set_option autoImplicit false

namespace CountingMatroid.Analysis.BoundedRunResourceEnvelope

open CountingMatroid.Model
open CountingMatroid.Model.Operations
open CountingMatroid.Model.Subroutines
open CountingMatroid.Analysis.RationalHeight

















/-- INTERNAL: The phase-power computation has polynomial nonoracle charge.
TEXLINE: main.tex:1384-1390 -/
theorem ratPower_otherSteps_le (q : ℚ) (j : ℕ) :
    otherSteps (CountingMatroid.Program.ratPower q j) ≤
      j * (binaryRatLength 1 + j * binaryRatLength q) ^ 2 := by
  unfold CountingMatroid.Program.ratPower Arlib.Computation.Charged.repeatFor
  simpa using ratPower_fold_otherSteps_le q 1 (List.range j)







end CountingMatroid.Analysis.BoundedRunResourceEnvelope

end

section


set_option autoImplicit false
namespace CountingMatroid.Analysis.PhaseChainWork
open CountingMatroid.Model CountingMatroid.Model.Operations
open CountingMatroid.Model.Subroutines CountingMatroid.Program
open CountingMatroid.Analysis.ResourceBound
open CountingMatroid.Analysis.BoundedRunResourceEnvelope
open CountingMatroid.Analysis.ScheduleOtherStepsEnvelope

/-- INTERNAL: A pure computation contributes no nonoracle work. -/
@[simp] theorem work_pure {α : Type} (x : α) :
    otherSteps (pure x : Arlib.Computation.Charged Op Cell α) = 0 := by
  simp [otherSteps]

/-- INTERNAL: One charged word instruction contributes one nonoracle step. -/
@[simp] theorem work_word {α : Type} (i : Arlib.Computation.Op) (x : α) :
    otherSteps (Arlib.Computation.Charged.op (Op.word i) x) = 1 := by
  cases i <;> simp [otherSteps, Arlib.Computation.Op.all,
    Arlib.Computation.CostVec.one]

/-- INTERNAL: A batch of word instructions contributes its batch length. -/
@[simp] theorem work_words {α : Type} (i : Arlib.Computation.Op) (k : ℕ) (x : α) :
    otherSteps (Arlib.Computation.Charged.opMany (Op.word i) k x) = k := by
  cases i <;> simp [otherSteps, Arlib.Computation.Op.all,
    Arlib.Computation.CostVec.many]

/-- INTERNAL: A fair-bit read contributes one nonoracle step. -/
@[simp] theorem work_bit {α : Type} (x : α) :
    otherSteps (Arlib.Computation.Charged.op Op.fairBit x) = 1 := by
  simp [otherSteps, Arlib.Computation.Op.all, Arlib.Computation.CostVec.one]



/-- INTERNAL: Mapping a pure result preserves the charged work. -/
@[simp] theorem work_map {α β : Type} (f : α → β)
    (p : Arlib.Computation.Charged Op Cell α) : otherSteps (f <$> p) = otherSteps p := by
  simp only [otherSteps, Arlib.Computation.Charged.cost_map]

















end CountingMatroid.Analysis.PhaseChainWork

end

section


set_option autoImplicit false
namespace CountingMatroid.Analysis.RestartPhaseWork
open CountingMatroid.Model CountingMatroid.Model.Operations
open CountingMatroid.Model.Subroutines CountingMatroid.Program
open CountingMatroid.Analysis.ResourceBound
open CountingMatroid.Analysis.PhaseChainWork
open CountingMatroid.Analysis.BoundedRunResourceEnvelope
open CountingMatroid.Analysis.ScheduleOtherStepsEnvelope

/-- INTERNAL: A fresh transversal requires one bit, one insertion, and one
cursor increment per ground position. TEXLINE: main.tex:1431-1439 -/
theorem freshTransversal_otherSteps_le (n : ℕ) (tape : ℕ → Bool) (cursor : ℕ) :
    otherSteps (freshTransversal n tape cursor) ≤ n * (2 * n + 3) := by
  unfold freshTransversal
  apply (otherSteps_foldl_le_of_mem _ _ (2 * n + 3) ?_ _).trans_eq (by simp)
  intro acc i hi
  simp [otherSteps_bind, fairBit, insertPaired, successor]; omega




end CountingMatroid.Analysis.RestartPhaseWork

end
set_option autoImplicit false
namespace CountingMatroid.Analysis.RestartPhaseWork
end CountingMatroid.Analysis.RestartPhaseWork
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.RestartPhaseWork
open CountingMatroid.Model CountingMatroid.Model.Operations
open CountingMatroid.Model.Subroutines CountingMatroid.Program
open CountingMatroid.Analysis.ResourceBound
open CountingMatroid.Analysis.PhaseChainWork
open CountingMatroid.Analysis.BoundedRunResourceEnvelope
open CountingMatroid.Analysis.ScheduleOtherStepsEnvelope

/-- INTERNAL: Restart work is bounded by its explicit nested loop caps, powers,
table reads, and the uniform trace-call bound. TEXLINE: main.tex:1428-1439 -/
theorem solution {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (tape : ℕ → Bool) (s : AnnealingSchedule) (tables : LearnedWeights n)
    (j cursor K : ℕ)
    (hq : binaryRatLength 1 + n * (binaryRatLength 1 + j * binaryRatLength s.ρ) ≤ K)
    (hw : ∀ phase i, binaryRatLength (tables phase i) ≤ K) :
    otherSteps (restartPhase r o₁ o₂ tape s tables j cursor) ≤
      n * (2 * n + 3) + j *
        (1 + j * (binaryRatLength 1 + j * binaryRatLength s.ρ) ^ 2 +
          (s.L * n * n + 1) +
          s.τ * (s.restartCap *
            (chainBudget n s.drawTrials K + n * (4 * n + 3) + 3))) := by
  have htrace (index : ℕ) (hi : index < j) (current : RestartCursor n) :
      otherSteps (traceReturn r o₁ o₂ tape s (ratPower s.ρ (index + 1)).val
        (tables (index + 1)) current) ≤
        s.restartCap * (chainBudget n s.drawTrials K + n * (4 * n + 3) + 3) := by
    apply traceReturn_otherSteps_le r o₁ o₂ tape s _ _ current K _ (hw _)
    have hl := ratPower_binary_length_le s.ρ (index + 1)
    have hm := Nat.mul_le_mul_right (binaryRatLength s.ρ) (show index + 1 ≤ j by omega)
    have hn := Nat.mul_le_mul_left n (show binaryRatLength (ratPower s.ρ (index + 1)).val ≤
      binaryRatLength 1 + j * binaryRatLength s.ρ by omega)
    omega
  unfold restartPhase
  rw [otherSteps_bind, otherSteps_bind]
  have hf := freshTransversal_otherSteps_le n tape cursor
  split <;> simp only [work_pure, Nat.add_zero]
  all_goals
    apply Nat.add_le_add hf
    unfold Arlib.Computation.Charged.repeatFor
    apply (otherSteps_foldl_le_of_mem _ _
      (1 + j * (binaryRatLength 1 + j * binaryRatLength s.ρ) ^ 2 +
        (s.L * n * n + 1) +
        s.τ * (s.restartCap *
          (chainBudget n s.drawTrials K + n * (4 * n + 3) + 3))) ?_ _).trans_eq (by simp)
    intro acc index hi
    have hi' : index + 1 ≤ j := by simpa using hi
    cases acc with
    | none => simp
    | some current =>
        have hp : otherSteps (ratPower s.ρ (index + 1)) ≤
            j * (binaryRatLength 1 + j * binaryRatLength s.ρ) ^ 2 := by
          apply (ratPower_otherSteps_le s.ρ _).trans
          exact Nat.mul_le_mul hi' (Nat.pow_le_pow_left (by gcongr) 2)
        simp only [otherSteps_bind, successor, learnedWeightRead,
          Arlib.Computation.Charged.val_op, Arlib.Computation.Charged.val_opMany,
          work_word, work_words]
        have hsum : 1 + otherSteps (ratPower s.ρ (index + 1)) +
            (s.L * n * n + 1) ≤
            1 + j * (binaryRatLength 1 + j * binaryRatLength s.ρ) ^ 2 +
              (s.L * n * n + 1) := by omega
        rw [← Nat.add_assoc, ← Nat.add_assoc]
        apply Nat.add_le_add hsum
        try unfold Arlib.Computation.Charged.repeatFor
        apply (otherSteps_foldl_le_of_mem _ _
          (s.restartCap * (chainBudget n s.drawTrials K + n * (4 * n + 3) + 3))
          ?_ _).trans_eq (by simp)
        intro c a ha
        cases c with
        | none => simp
        | some c => exact htrace index (by omega) c
