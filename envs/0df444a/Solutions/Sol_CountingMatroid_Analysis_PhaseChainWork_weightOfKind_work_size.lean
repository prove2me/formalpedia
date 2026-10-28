-- Prove2me | solution 1 for CountingMatroid.Analysis.PhaseChainWork.weightOfKind_work_size
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T12:29:37.706996+00:00
-- url     : https://prove2.me/submissions/24309cd1-0df0-47dd-b494-ea7835689040

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
import Theorems.Thm_CountingMatroid_Analysis_BoundedRunResourceEnvelope_ratPower_binary_length_le
import Theorems.Thm_CountingMatroid_Analysis_BoundedRunResourceEnvelope_ratPower_fold_otherSteps_le
import Theorems.Thm_CountingMatroid_Analysis_PhaseChainWork_greedyRank_otherSteps_le
import Theorems.Thm_CountingMatroid_Analysis_ScheduleOtherStepsEnvelope_binaryRatLength_mul_le

namespace CountingMatroid.Analysis.ResourceBound
end CountingMatroid.Analysis.ResourceBound
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

section


set_option autoImplicit false

namespace CountingMatroid.Analysis.BoundedRunResourceEnvelope

open CountingMatroid.Model
open CountingMatroid.Model.Operations
open CountingMatroid.Model.Subroutines
open CountingMatroid.Analysis.RationalHeight













/-- INTERNAL: The charged rational product costs at most the square of the
operand encoding lengths. TEXLINE: main.tex:1384-1390 -/
theorem otherSteps_ratMul_le (a b : ℚ) :
    otherSteps (ratMul a b) ≤ (binaryRatLength a + binaryRatLength b) ^ 2 := by
  simp only [otherSteps, ratMul, Arlib.Computation.Charged.cost_opMany,
    Arlib.Computation.CostVec.many]
  simp [Arlib.Computation.Op.all, binaryRatLength, binaryNatLength]
  change ((a.num.natAbs.log2 + a.den.log2 + 3) +
    (b.num.natAbs.log2 + b.den.log2 + 3)) ^ 2 ≤ _
  apply Nat.pow_le_pow_left
  omega



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





/-- INTERNAL: Mapping a pure result preserves the charged work. -/
@[simp] theorem work_map {α β : Type} (f : α → β)
    (p : Arlib.Computation.Charged Op Cell α) : otherSteps (f <$> p) = otherSteps p := by
  simp only [otherSteps, Arlib.Computation.Charged.cost_map]




/-- INTERNAL: Projecting a paired state costs linear scan work times membership
cost. TEXLINE: main.tex:1333-1346 -/
theorem pairedProjections_otherSteps_le {n : ℕ} (state : PairedSet n) :
    otherSteps (pairedProjections state) ≤ n * (4 * n + 4) := by
  unfold pairedProjections
  apply (otherSteps_foldl_le_of_mem _ _ (4 * n + 4) ?_ _).trans_eq (by simp)
  intro acc i hi
  simp only [otherSteps_bind]
  split <;> simp only [otherSteps_bind]
  all_goals split <;> simp [otherSteps_bind, containsPaired, insertElement, successor]
  all_goals omega

/-- INTERNAL: The paired-rank evaluation uses two bounded greedy scans and
bounded projection work. TEXLINE: main.tex:1333-1346 -/
theorem pairedRank_otherSteps_le {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (state : PairedSet n) : otherSteps (pairedRank r o₁ o₂ state) ≤ 8 * (n + 1) ^ 3 := by
  unfold pairedRank
  simp only [otherSteps_bind, work_map]
  have hp := pairedProjections_otherSteps_le state
  have h₁ := greedyRank_otherSteps_le false o₁ (pairedProjections state).val.1
  have h₂ := greedyRank_otherSteps_le true o₂ (pairedProjections state).val.2.1
  simp only [natAdd, natSub, work_word]
  nlinarith [sq_nonneg (n : ℤ)]










end CountingMatroid.Analysis.PhaseChainWork

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

/-- INTERNAL: State weights have bounded size and work for arbitrary oracle
answers and bounded input multipliers. TEXLINE: main.tex:1384-1390 -/
theorem solution {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (q : ℚ) (weights : Multipliers n) (state : PairedSet n) (kind : StateKind n)
    (K : ℕ) (hq : binaryRatLength 1 + n * binaryRatLength q ≤ K)
    (hw : ∀ i, binaryRatLength (weights i) ≤ K) :
    otherSteps (weightOfKind r o₁ o₂ q weights state kind) ≤
      8 * (n + 1) ^ 3 + (n + 4) * K ^ 2 + n * n + 2 ∧
    (∀ w, (weightOfKind r o₁ o₂ q weights state kind).val = some w →
      binaryRatLength w ≤ 2 * K) := by
  have hd : (natSub n (pairedRank r o₁ o₂ state).val).val ≤ n := Nat.sub_le _ _
  have hl : binaryRatLength
      (ratPower q (natSub n (pairedRank r o₁ o₂ state).val).val).val ≤ K := by
    have hp := ratPower_binary_length_le q (natSub n (pairedRank r o₁ o₂ state).val).val
    have hm := Nat.mul_le_mul_right (binaryRatLength q) hd
    omega
  have hc : otherSteps
      (ratPower q (natSub n (pairedRank r o₁ o₂ state).val).val) ≤ n * K ^ 2 := by
    apply (ratPower_otherSteps_le q _).trans
    exact Nat.mul_le_mul hd (Nat.pow_le_pow_left (by
      have hm := Nat.mul_le_mul_right (binaryRatLength q) hd
      omega) 2)
  have hr := pairedRank_otherSteps_le r o₁ o₂ state
  cases kind with
  | invalid => simp [weightOfKind]
  | transversal =>
      constructor
      · simp only [weightOfKind, otherSteps_bind, work_map, natSub, work_word, work_pure]
        simp only [natSub, Arlib.Computation.Charged.val_op] at hc ⊢
        nlinarith
      · intro w he
        simp only [weightOfKind, Arlib.Computation.Charged.val_bind,
          Arlib.Computation.Charged.val_pure, Option.some.injEq] at he
        subst w
        exact hl.trans (by omega)
  | defect i k =>
      by_cases hik : i ≠ k
      · have hm := otherSteps_ratMul_le (weights ⟨i, k, hik⟩)
          (ratPower q (natSub n (pairedRank r o₁ o₂ state).val).val).val
        have hml := binaryRatLength_mul_le (weights ⟨i, k, hik⟩)
          (ratPower q (natSub n (pairedRank r o₁ o₂ state).val).val).val
        have hi := hw ⟨i, k, hik⟩
        have hmc : otherSteps (ratMul (weights ⟨i, k, hik⟩)
            (ratPower q (natSub n (pairedRank r o₁ o₂ state).val).val).val) ≤
            4 * K ^ 2 := by
          apply hm.trans
          calc
            _ ≤ (2 * K) ^ 2 := Nat.pow_le_pow_left (by omega) 2
            _ = _ := by ring
        constructor
        · simp only [weightOfKind, dif_pos hik, otherSteps_bind, work_map,
            multiplierRead, Arlib.Computation.Charged.val_opMany, work_words,
            natSub, work_word, work_pure]
          simp only [natSub, Arlib.Computation.Charged.val_op] at hc hmc ⊢
          nlinarith
        · intro w he
          simp only [weightOfKind, dif_pos hik, Arlib.Computation.Charged.val_bind,
            ratMul, multiplierRead, Arlib.Computation.Charged.val_opMany,
            Arlib.Computation.Charged.val_pure, Option.some.injEq] at he
          subst w
          omega
      · simp [weightOfKind, hik]
