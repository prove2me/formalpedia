-- Prove2me | solution 1 for CountingMatroid.Analysis.PhaseChainWork.chainStep_otherSteps_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T14:09:14.144758+00:00
-- url     : https://prove2.me/submissions/d555bf02-2551-44a6-8b37-566813c0ec3c

import Mathlib.Tactic.ClearExcept
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
import Theorems.Thm_CountingMatroid_Analysis_PhaseChainWork_boundedUniform_otherSteps_le
import Theorems.Thm_CountingMatroid_Analysis_PhaseChainWork_classifyState_otherSteps_le
import Theorems.Thm_CountingMatroid_Analysis_PhaseChainWork_selectPaired_otherSteps_le
import Theorems.Thm_CountingMatroid_Analysis_PhaseChainWork_weightOfKind_work_size
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



/-- INTERNAL: A charged rational comparison costs at most the sum of the
operand encoding lengths. -/
theorem ratLess_otherSteps_le (a b : ℚ) :
    otherSteps (ratLess a b) ≤ binaryRatLength a + binaryRatLength b := by
  simp only [otherSteps, ratLess, Arlib.Computation.Charged.cost_opMany]
  simp [Arlib.Computation.Op.all, Arlib.Computation.CostVec.many,
    binaryRatLength, binaryNatLength]
  change a.num.natAbs.log2 + a.den.log2 + 3 +
    (b.num.natAbs.log2 + b.den.log2 + 3) ≤ _
  omega











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















/-- INTERNAL: Rational inversion swaps numerator and denominator lengths. -/
theorem binaryRatLength_inv_eq (q : ℚ) :
    binaryRatLength q⁻¹ = binaryRatLength q := by
  by_cases hz : q.num = 0
  · have hq : q = 0 := Rat.zero_of_num_zero hz
    simp [hq]
  · unfold binaryRatLength binaryNatLength
    simp [Rat.num_inv, Rat.den_inv, Int.natAbs_mul,
      Int.natAbs_sign, hz, Int.natAbs_natCast]
    omega

/-- INTERNAL: Rational division adds no more binary encoding length than
multiplication by the denominator's reciprocal. -/
theorem binaryRatLength_div_le (q s : ℚ) :
    binaryRatLength (q / s) ≤ binaryRatLength q + binaryRatLength s := by
  rw [div_eq_mul_inv]
  simpa only [binaryRatLength_inv_eq] using binaryRatLength_mul_le q s⁻¹

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

set_option maxHeartbeats 800000 in
/-- INTERNAL: Each capped Metropolis step has polynomial nonoracle work, even
when an exchange is invalid or any rejection draw aborts.
TEXLINE: main.tex:1333-1346,1384-1421 -/
theorem solution {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (tape : ℕ → Bool) (trials : ℕ) (q : ℚ) (weights : Multipliers n)
    (state : PairedSet n) (cursor K : ℕ)
    (hq : binaryRatLength 1 + n * binaryRatLength q ≤ K)
    (hw : ∀ i, binaryRatLength (weights i) ≤ K) :
    otherSteps (chainStep r o₁ o₂ tape trials q weights state cursor) ≤
      chainBudget n trials K := by
  unfold chainBudget
  have hK : 4 ≤ K := by
    have hone : binaryRatLength (1 : ℚ) = 4 := by decide
    omega
  have hlog : n.log2 ≤ n := by
    simpa only [Nat.log2_eq_log_two] using Nat.log_le_self 2 n
  have hdraw (v c : ℕ) (hv : v.log2 ≤ 4 * K + n) :
      otherSteps (boundedUniform tape trials v c) ≤
        3 + trials * (3 * (4 * K + n + 1) + 2) := by
    exact (boundedUniform_otherSteps_le tape trials v c).trans
      (Nat.add_le_add_left (Nat.mul_le_mul_left trials (by omega)) 3)
  have hsel (occupied : Bool) (k : ℕ) := selectPaired_otherSteps_le state occupied k
  have hkind (x : PairedSet n) := classifyState_otherSteps_le x
  have hweight (x : PairedSet n) (kind : StateKind n) :=
    weightOfKind_work_size r o₁ o₂ q weights x kind K hq hw
  have haccept (old new : ℚ) (x y : PairedSet n) (c : ℕ)
      (ho : binaryRatLength old ≤ 2 * K) (hn : binaryRatLength new ≤ 2 * K) :
      otherSteps (do
        let ratio ← ratDiv new old
        let needsDraw ← ratLess ratio 1
        if needsDraw then
          let denominator ← rationalDenominator ratio
          let numerator ← rationalNumerator ratio
          let acceptedDraw ← boundedUniform tape trials denominator c
          match acceptedDraw.1 with
          | none => pure none
          | some value =>
              let accepted ← lessThan value numerator
              if accepted then pure (some (y, acceptedDraw.2))
              else pure (some (x, acceptedDraw.2))
        else pure (some (y, c))) ≤
        16 * K ^ 2 + 12 * K + 5 +
          (3 + trials * (3 * (4 * K + n + 1) + 2)) := by
    have hr : binaryRatLength (ratDiv new old).val ≤ 4 * K := by
      have := binaryRatLength_div_le new old
      simpa only [ratDiv, Arlib.Computation.Charged.val_opMany] using
        (this.trans (by omega))
    have hdiv : otherSteps (ratDiv new old) ≤ 16 * K ^ 2 := by
      have hb := rationalBinary_otherSteps_le .udiv new old (new / old)
      apply hb.trans
      calc
        _ ≤ (4 * K) ^ 2 := Nat.pow_le_pow_left (by omega) 2
        _ = _ := by ring
    have hless := ratLess_otherSteps_le (ratDiv new old).val 1
    have hden : otherSteps (rationalDenominator (ratDiv new old).val) ≤ 4 * K := by
      simp only [rationalDenominator, work_words]
      change (ratDiv new old).val.num.natAbs.log2 +
        (ratDiv new old).val.den.log2 + 3 ≤ 4 * K
      unfold binaryRatLength binaryNatLength at hr
      omega
    have hnum : otherSteps (rationalNumerator (ratDiv new old).val) ≤ 4 * K := by
      simp only [rationalNumerator, work_words]
      change (ratDiv new old).val.num.natAbs.log2 +
        (ratDiv new old).val.den.log2 + 3 ≤ 4 * K
      unfold binaryRatLength binaryNatLength at hr
      omega
    have hd := hdraw (rationalDenominator (ratDiv new old).val).val c (by
      simp only [rationalDenominator, Arlib.Computation.Charged.val_opMany]
      unfold binaryRatLength binaryNatLength at hr
      omega)
    simp only [otherSteps_bind]
    split
    · simp only [otherSteps_bind]
      split
      · simp only [work_pure, Nat.add_zero]
        have hone : binaryRatLength (1 : ℚ) = 4 := by decide
        omega
      · simp only [otherSteps_bind]
        split <;> simp only [lessThan, work_word, work_pure, Nat.add_zero]
        all_goals have hone : binaryRatLength (1 : ℚ) = 4 := by decide
        all_goals omega
    · simp only [work_pure, Nat.add_zero]
      have hone : binaryRatLength (1 : ℚ) = 4 := by decide
      omega
  have hpairs (x y : PairedSet n) (kx ky : StateKind n) (c : ℕ) :
      otherSteps (do
        let oldWeight ← weightOfKind r o₁ o₂ q weights x kx
        let newWeight ← weightOfKind r o₁ o₂ q weights y ky
        match oldWeight, newWeight with
        | some oldWeight, some newWeight => do
            let ratio ← ratDiv newWeight oldWeight
            let needsDraw ← ratLess ratio 1
            if needsDraw then
              let denominator ← rationalDenominator ratio
              let numerator ← rationalNumerator ratio
              let acceptedDraw ← boundedUniform tape trials denominator c
              match acceptedDraw.1 with
              | none => pure none
              | some value =>
                  let accepted ← lessThan value numerator
                  if accepted then pure (some (y, acceptedDraw.2))
                  else pure (some (x, acceptedDraw.2))
            else pure (some (y, c))
        | _, _ => pure none) ≤
        2 * (8 * (n + 1) ^ 3 + (n + 4) * K ^ 2 + n * n + 2) +
        16 * K ^ 2 + 12 * K + 5 +
          (3 + trials * (3 * (4 * K + n + 1) + 2)) := by
    have hx := hweight x kx
    have hy := hweight y ky
    simp only [otherSteps_bind]
    split
    · rename_i old new ho hn
      have ha := haccept old new x y c (hx.2 old ho) (hy.2 new hn)
      omega
    · simp only [work_pure]
      omega
  unfold chainStep
  simp only [otherSteps_bind]
  split
  · simp [fairBit, successor]
  · have hd₁ := hdraw n (successor cursor).val (by omega)
    simp only [otherSteps_bind]
    split
    · simp only [work_pure, Nat.add_zero, fairBit, successor, work_word, work_bit,
        Arlib.Computation.Charged.val_op] at hd₁ ⊢
      omega
    · rename_i aIndex haIndex
      have hd₂ := hdraw n (boundedUniform tape trials n (successor cursor).val).val.2
        (by omega)
      simp only [otherSteps_bind]
      split
      · simp only [work_pure, Nat.add_zero, fairBit, successor, work_word, work_bit,
          Arlib.Computation.Charged.val_op] at hd₁ hd₂ ⊢
        omega
      · rename_i bIndex hbIndex
        have hs₁ := hsel true aIndex
        have hs₂ := hsel false bIndex
        simp only [otherSteps_bind]
        split
        · rename_i a b ha hb
          have hk := hkind (insertPaired (erasePaired state a).val b).val
          simp only [otherSteps_bind]
          split
          · simp only [work_pure, Nat.add_zero, fairBit, successor, erasePaired,
              insertPaired, work_word, work_words, work_bit,
              Arlib.Computation.Charged.val_op] at hd₁ hd₂ hs₁ hs₂ hk ⊢
            omega
          · have hkold := hkind state
            have hp := hpairs state (insertPaired (erasePaired state a).val b).val
              (classifyState state).val
              (classifyState (insertPaired (erasePaired state a).val b).val).val
              (boundedUniform tape trials n
                (boundedUniform tape trials n (successor cursor).val).val.2).val.2
            rw [otherSteps_bind] 
            simp only [fairBit, successor, erasePaired, insertPaired,
              work_word, work_words, work_bit, Arlib.Computation.Charged.val_op,
              Arlib.Computation.Charged.val_opMany] at hd₁ hd₂ hs₁ hs₂ hk hp ⊢
            simp only [otherSteps_bind] at hp ⊢
            clear hdraw hsel hkind hweight haccept hpairs hw
            cases ho : (weightOfKind r o₁ o₂ q weights state (classifyState state).val).val <;>
              cases hn : (weightOfKind r o₁ o₂ q weights
                (insert b (Finset.erase state a))
                (classifyState (insert b (Finset.erase state a))).val).val <;>
              simp only [ho, hn, work_pure] at hp ⊢
            case none.none => omega
            case none.some new => omega
            case some.none old => omega
            case some.some old new =>
              simp only [otherSteps_bind] at hp ⊢
              by_cases hneed : (ratLess (ratDiv new old).val 1).val = true
              · simp only [hneed, Bool.false_eq_true, ↓reduceIte, otherSteps_bind] at hp ⊢
                cases hchosen : (boundedUniform tape trials
                    (rationalDenominator (ratDiv new old).val).val
                    (boundedUniform tape trials n
                      (boundedUniform tape trials n (cursor + 1)).val.2).val.2).val.1 with
                | none =>
                    simp only [hchosen, work_pure] at hp ⊢
                    clear ho hn hneed hchosen
                    omega
                | some pick =>
                    simp only [hchosen, otherSteps_bind] at hp ⊢
                    by_cases haccepted :
                        (lessThan pick (rationalNumerator (ratDiv new old).val).val).val = true <;>
                      simp only [haccepted, Bool.false_eq_true, ↓reduceIte, work_pure] at hp ⊢ <;>
                      clear ho hn hneed hchosen haccepted
                    all_goals
                      have arithmetic (d₁ d₂ s₁ s₂ k₁ k₂ p A B C D E : Nat)
                          (hd₁ : d₁ ≤ A) (hd₂ : d₂ ≤ A) (hs₁ : s₁ ≤ B) (hs₂ : s₂ ≤ B)
                          (hk₁ : k₁ ≤ C) (hk₂ : k₂ ≤ C) (hp : p ≤ D + A) :
                          1 + (1 + (d₁ + (d₂ + (s₁ + (s₂ + (E + (E + (k₁ + (k₂ + p))))))))) ≤
                            2 + 3 * A + 2 * B + 2 * E + 2 * C + D := by
                        clear * - hd₁ hd₂ hs₁ hs₂ hk₁ hk₂ hp
                        omega
                      apply le_trans (arithmetic _ _ _ _ _ _ _ _ _ _ _ (2 * n + 1)
                        hd₁ hd₂ hs₁ hs₂ hk hkold hp)
                      clear * -
                      omega
              · simp only [hneed, Bool.false_eq_true, ↓reduceIte, work_pure] at hp ⊢
                clear ho hn hneed
                omega
        · simp only [work_pure, Nat.add_zero, fairBit, successor, work_word, work_bit,
            Arlib.Computation.Charged.val_op] at hd₁ hd₂ hs₁ hs₂ ⊢
          omega
