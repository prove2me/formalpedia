-- Prove2me | solution 1 for CountingMatroid.Analysis.BoundedRunResourceEnvelope.ratPower_fold_otherSteps_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T12:20:13.147134+00:00
-- url     : https://prove2.me/submissions/0d926ec4-9095-4de7-9fe3-fef585516a3b

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
import Theorems.Thm_CountingMatroid_Analysis_ScheduleOtherStepsEnvelope_binaryRatLength_mul_le

namespace CountingMatroid.Analysis.BoundedRunResourceEnvelope
end CountingMatroid.Analysis.BoundedRunResourceEnvelope
namespace CountingMatroid.Analysis.ScheduleOtherStepsEnvelope
end CountingMatroid.Analysis.ScheduleOtherStepsEnvelope
namespace CountingMatroid.Analysis.LeastHalvingsCost
end CountingMatroid.Analysis.LeastHalvingsCost
namespace CountingMatroid.Analysis.ResourceBound
end CountingMatroid.Analysis.ResourceBound
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

/-- INTERNAL: Every intermediate value in a charged rational-power fold has
bounded encoding length, giving a uniform per-step charge.
TEXLINE: main.tex:1384-1390 -/
theorem solution (q acc : ℚ) (l : List ℕ) :
    otherSteps (Arlib.Computation.Charged.foldl
      (fun current _ => ratMul current q) l acc) ≤
      l.length * (binaryRatLength acc + l.length * binaryRatLength q) ^ 2 := by
  induction l generalizing acc with
  | nil => simp [otherSteps]
  | cons i rest ih =>
      rw [show Arlib.Computation.Charged.foldl
        (fun current _ => ratMul current q) (i :: rest) acc =
        ratMul acc q >>= fun next => Arlib.Computation.Charged.foldl
          (fun current _ => ratMul current q) rest next from rfl,
        CountingMatroid.Analysis.ResourceBound.otherSteps_bind]
      have hhead := otherSteps_ratMul_le acc q
      have htail := ih (acc * q)
      have hlength :=
        CountingMatroid.Analysis.ScheduleOtherStepsEnvelope.binaryRatLength_mul_le acc q
      simp only [ratMul] at htail
      simp only [List.length_cons]
      have hsmall : binaryRatLength acc + binaryRatLength q ≤
          binaryRatLength acc + (rest.length + 1) * binaryRatLength q := by
        nlinarith
      have hlarge : binaryRatLength (acc * q) +
          rest.length * binaryRatLength q ≤
          binaryRatLength acc + (rest.length + 1) * binaryRatLength q := by
        nlinarith
      have hfirst := (hhead.trans (Nat.pow_le_pow_left hsmall 2))
      have hremaining := Nat.mul_le_mul_left rest.length
        (Nat.pow_le_pow_left hlarge 2)
      calc
        otherSteps (ratMul acc q) +
          otherSteps (Arlib.Computation.Charged.foldl
            (fun current _ => ratMul current q) rest (acc * q)) ≤
          (binaryRatLength acc + binaryRatLength q) ^ 2 +
            rest.length * (binaryRatLength (acc * q) +
              rest.length * binaryRatLength q) ^ 2 := Nat.add_le_add hhead htail
        _ ≤ (binaryRatLength acc + (rest.length + 1) * binaryRatLength q) ^ 2 +
            rest.length * (binaryRatLength acc +
              (rest.length + 1) * binaryRatLength q) ^ 2 :=
          Nat.add_le_add (Nat.pow_le_pow_left hsmall 2) hremaining
        _ = (rest.length + 1) *
            (binaryRatLength acc + (rest.length + 1) * binaryRatLength q) ^ 2 := by
          ring
