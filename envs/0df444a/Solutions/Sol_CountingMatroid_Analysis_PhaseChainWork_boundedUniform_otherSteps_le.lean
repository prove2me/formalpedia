-- Prove2me | solution 1 for CountingMatroid.Analysis.PhaseChainWork.boundedUniform_otherSteps_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T12:27:03.72198+00:00
-- url     : https://prove2.me/submissions/993005bc-27ec-4bc5-b85a-f2cbce8a6dc6

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
import Definitions.Def_CountingMatroid_Analysis_PhaseChainWork
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

namespace CountingMatroid.Analysis.ResourceBound
end CountingMatroid.Analysis.ResourceBound
namespace CountingMatroid.Analysis.BoundedRunResourceEnvelope
end CountingMatroid.Analysis.BoundedRunResourceEnvelope
namespace CountingMatroid.Analysis
end CountingMatroid.Analysis
namespace CountingMatroid.Meta
end CountingMatroid.Meta
namespace Arlib
end Arlib
namespace CountingMatroid.Analysis.ScheduleOtherStepsEnvelope
end CountingMatroid.Analysis.ScheduleOtherStepsEnvelope
namespace CountingMatroid.Analysis.LeastHalvingsCost
end CountingMatroid.Analysis.LeastHalvingsCost
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

/-- INTERNAL: The word-operation fold in `otherSteps` distributes over
two charged cost vectors. -/
theorem foldl_word_add (l : List Arlib.Computation.Op)
    (f g : Arlib.Computation.Op → ℕ) :
    ∀ a b, l.foldl (fun z x => z + (f x + g x)) (a + b) =
      l.foldl (fun z x => z + f x) a + l.foldl (fun z x => z + g x) b := by
  induction l with
  | nil => simp
  | cons x xs ih =>
      intro a b
      simpa [List.foldl, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        ih (a + f x) (b + g x)

/-- INTERNAL: Nonoracle charges add when charged computations are sequenced. -/
theorem otherSteps_bind {α β : Type}
    (p : Arlib.Computation.Charged Op Cell α)
    (f : α → Arlib.Computation.Charged Op Cell β) :
    otherSteps (p >>= f) = otherSteps p + otherSteps (f p.val) := by
  simp only [otherSteps, Arlib.Computation.Charged.cost_bind, Pi.add_apply]
  have h := foldl_word_add Arlib.Computation.Op.all
    (fun x => p.cost (Op.word x)) (fun x => (f p.val).cost (Op.word x)) 0 0
  simp only [Nat.zero_add] at h
  rw [h]
  omega

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
set_option autoImplicit false
namespace CountingMatroid.Analysis.PhaseChainWork
end CountingMatroid.Analysis.PhaseChainWork
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.PhaseChainWork
open CountingMatroid.Model CountingMatroid.Model.Operations
open CountingMatroid.Model.Subroutines CountingMatroid.Program
open CountingMatroid.Analysis.ResourceBound
open CountingMatroid.Analysis.BoundedRunResourceEnvelope
open CountingMatroid.Analysis.ScheduleOtherStepsEnvelope

/-- INTERNAL: Hard-capped rejection sampling has a uniform bound independent
of the tape and cursor. TEXLINE: main.tex:1392-1421 -/
theorem solution (tape : ℕ → Bool) (trials v cursor : ℕ) :
    otherSteps (boundedUniform tape trials v cursor) ≤
      3 + trials * (3 * (v.log2 + 1) + 2) := by
  have hwidth : (v - 1).log2 + 1 ≤ v.log2 + 1 := by
    simp only [Nat.log2_eq_log_two]
    exact Nat.add_le_add_right (Nat.log_mono_right (Nat.sub_le v 1)) 1
  have hinner (width cursor : ℕ) (acc : ℕ × ℕ) :
      otherSteps (Arlib.Computation.Charged.repeatFor (fun _ inner => do
        let bit ← fairBit tape inner.2
        let value ← appendBit inner.1 bit
        let next ← successor inner.2
        pure (value, next)) width acc) ≤ width * 3 := by
    unfold Arlib.Computation.Charged.repeatFor
    apply (otherSteps_foldl_le_of_mem _ _ 3 ?_ acc).trans_eq (by simp)
    intro b a ha
    simp [otherSteps_bind, fairBit, appendBit, successor]
  unfold boundedUniform
  simp only [otherSteps_bind]
  split
  · simp [lessThan]; omega
  · simp only [otherSteps_bind]
    split
    · simp [lessThan]; omega
    · simp only [otherSteps_bind]
      have hout := otherSteps_foldl_le_of_mem
        (fun (acc : Option ℕ × ℕ) (_ : ℕ) => do
          let done ← isSome acc.1
          if done then pure acc
          else
            let trial ← Arlib.Computation.Charged.repeatFor (fun _ inner => do
              let bit ← fairBit tape inner.2
              let value ← appendBit inner.1 bit
              let next ← successor inner.2
              pure (value, next)) (uniformWidth v).val (0, acc.2)
            let accepted ← lessThan trial.1 v
            if accepted then pure (some trial.1, trial.2)
            else pure (none, trial.2)) (List.range trials)
        (3 * (v.log2 + 1) + 2) ?_ (none, cursor)
      · simpa only [lessThan, uniformWidth, work_word,
          Arlib.Computation.Charged.val_op, List.length_range,
          Arlib.Computation.Charged.repeatFor, ← Nat.add_assoc] using Nat.add_le_add_left hout 3
      · intro acc a ha
        simp only [otherSteps_bind]
        split
        · simp [isSome]
        · have hi := hinner (uniformWidth v).val acc.2 (0, acc.2)
          simp only [otherSteps_bind]
          split <;> simp only [work_pure, Nat.add_zero]
          all_goals simp only [isSome, lessThan, work_word] at *
          all_goals simp only [uniformWidth, Arlib.Computation.Charged.val_op] at hi ⊢
          all_goals nlinarith
