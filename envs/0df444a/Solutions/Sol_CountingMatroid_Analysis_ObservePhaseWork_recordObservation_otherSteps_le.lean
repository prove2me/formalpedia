-- Prove2me | solution 1 for CountingMatroid.Analysis.ObservePhaseWork.recordObservation_otherSteps_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T12:56:25.808435+00:00
-- url     : https://prove2.me/submissions/0a7b77c5-ca47-4907-8fa6-a4559a15bfa4

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
import Definitions.Def_CountingMatroid_Analysis_ObservePhaseWork
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
import Theorems.Thm_CountingMatroid_Analysis_PhaseChainWork_classifyState_otherSteps_le
import Theorems.Thm_CountingMatroid_Analysis_PhaseChainWork_greedyRank_otherSteps_le

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

namespace CountingMatroid.Analysis.ScheduleOtherStepsEnvelope

open CountingMatroid.Model
open CountingMatroid.Model.Subroutines



















/-- INTERNAL: A charged rational binary operation is bounded by its input encodings. -/
theorem rationalBinary_otherSteps_le (instr : Arlib.Computation.Op)
    (a b result : ℚ) :
    otherSteps (Arlib.Computation.Charged.opMany
      (CountingMatroid.Model.Operations.Op.word instr)
      ((a.num.natAbs.log2 + a.den.log2 + 3 +
        (b.num.natAbs.log2 + b.den.log2 + 3)) ^ 2) result) ≤
      (binaryRatLength a + binaryRatLength b) ^ 2 := by
  have hcost (z : ℕ) : otherSteps
      (Arlib.Computation.Charged.opMany
        (CountingMatroid.Model.Operations.Op.word instr) z result) = z := by
    cases instr <;> simp [otherSteps, Arlib.Computation.Op.all,
      Arlib.Computation.CostVec.many]
  rw [hcost]
  unfold binaryRatLength binaryNatLength
  apply Nat.pow_le_pow_left
  omega













end CountingMatroid.Analysis.ScheduleOtherStepsEnvelope

end

section


set_option autoImplicit false

namespace CountingMatroid.Analysis.RationalHeight
open CountingMatroid.Model





/-- INTERNAL: Two component lengths bound the rational encoding length. -/
theorem binaryRatLength_le_height (q : ℚ) :
    binaryRatLength q ≤ 2 * rationalHeight q + 2 := by
  unfold rationalHeight binaryRatLength binaryNatLength
  omega




end CountingMatroid.Analysis.RationalHeight

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
namespace CountingMatroid.Analysis.ObservePhaseWork
end CountingMatroid.Analysis.ObservePhaseWork
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.ObservePhaseWork
open CountingMatroid.Model CountingMatroid.Model.Operations
open CountingMatroid.Model.Subroutines CountingMatroid.Program
open CountingMatroid.Analysis.ResourceBound
open CountingMatroid.Analysis.PhaseChainWork
open CountingMatroid.Analysis.BoundedRunResourceEnvelope
open CountingMatroid.Analysis.ScheduleOtherStepsEnvelope
open CountingMatroid.Analysis.RationalHeight

/-- INTERNAL: Recording an observation has bounded charge when the current
accumulator has bounded height. TEXLINE: main.tex:1362-1378 -/
theorem solution {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (rho : ℚ) (current : ObservationCursor n)
    (H : ℕ) (hh : rationalHeight current.numeratorSum ≤ H) :
    otherSteps (recordObservation r o₁ o₂ rho current) ≤
      recordBudget n (binaryRatLength rho) H := by
  have hone : binaryRatLength (1 : ℚ) = 4 := by decide
  have hl := ratPower_binary_length_le rho
    (natSub n (pairedRank r o₁ o₂ current.state).val).val
  have hm := Nat.mul_le_mul_right (binaryRatLength rho)
    (Nat.sub_le n (pairedRank r o₁ o₂ current.state).val)
  have hs := binaryRatLength_le_height current.numeratorSum
  have hp : otherSteps (ratPower rho (natSub n (pairedRank r o₁ o₂ current.state).val).val) ≤
      n * (4 + n * binaryRatLength rho) ^ 2 := by
    apply (ratPower_otherSteps_le rho _).trans
    apply Nat.mul_le_mul (Nat.sub_le _ _) (Nat.pow_le_pow_left _ 2)
    simpa only [hone, natSub, Arlib.Computation.Charged.val_op] using Nat.add_le_add_left hm (binaryRatLength 1)
  have ha := rationalBinary_otherSteps_le .add current.numeratorSum
    (ratPower rho (natSub n (pairedRank r o₁ o₂ current.state).val).val).val
    (current.numeratorSum +
      (ratPower rho (natSub n (pairedRank r o₁ o₂ current.state).val).val).val)
  have ha' : otherSteps (ratAdd current.numeratorSum
      (ratPower rho (natSub n (pairedRank r o₁ o₂ current.state).val).val).val) ≤
      (2 * H + 2 + (4 + n * binaryRatLength rho)) ^ 2 := by
    apply ha.trans
    apply Nat.pow_le_pow_left _ 2
    simp only [natSub, Arlib.Computation.Charged.val_op] at hl ⊢
    omega
  have hr := pairedRank_otherSteps_le r o₁ o₂ current.state
  have hc := classifyState_otherSteps_le current.state
  unfold recordObservation recordBudget
  rw [otherSteps_bind]
  split
  · simp; omega
  · simp [otherSteps_bind, countIncrement]; omega
  · simp only [otherSteps_bind, work_pure, Nat.add_zero, countIncrement, work_words,
      natSub, work_word, Arlib.Computation.Charged.val_op]
    simp only [natSub, Arlib.Computation.Charged.val_op] at hp ha'
    omega
