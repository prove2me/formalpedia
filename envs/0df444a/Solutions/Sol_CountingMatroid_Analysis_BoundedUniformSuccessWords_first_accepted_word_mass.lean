-- Prove2me | solution 1 for CountingMatroid.Analysis.BoundedUniformSuccessWords.first_accepted_word_mass
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T16:15:22.759014+00:00
-- url     : https://prove2.me/submissions/ef6b7c5c-2879-4b4c-8c29-052f10795151

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
import Definitions.Def_CountingMatroid_Analysis_BoundedUniformAbortMass
import Definitions.Def_CountingMatroid_Analysis_BoundedUniformReplay
import Definitions.Def_CountingMatroid_Analysis_ChainStepIntervalReplay
import Definitions.Def_CountingMatroid_Analysis_FiniteStoppedFiberMass
import Definitions.Def_CountingMatroid_Analysis_FirstPhaseFailure
import Definitions.Def_CountingMatroid_Analysis_RelativeObservationBounds
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
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Combinatorics.Matroid.Rank.ENat
import Mathlib.Data.BitVec
import Mathlib.Data.ENNReal.Inv
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Vector
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Infix
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Sort
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Card.Arithmetic
import Mathlib.Data.Set.Finite.List
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Ring.RingNF
import Theorems.Thm_CountingMatroid_Analysis_BoundedUniformSuccessWords_read_word_bijective
import Theorems.Thm_CountingMatroid_Analysis_BoundedUniformSuccessWords_read_word_rejected_sum
import Theorems.Thm_CountingMatroid_Analysis_FiniteStoppedFiberMass_fairMass_split

namespace CountingMatroid.Analysis.BoundedUniformSuccessWords
end CountingMatroid.Analysis.BoundedUniformSuccessWords
namespace CountingMatroid.Meta
end CountingMatroid.Meta
namespace Arlib
end Arlib
namespace CountingMatroid.Analysis.FiniteObservationMarkov
end CountingMatroid.Analysis.FiniteObservationMarkov
namespace CountingMatroid.Analysis.FiniteTapePrefixBound
end CountingMatroid.Analysis.FiniteTapePrefixBound
namespace CountingMatroid.Analysis.InitialRestartLaw
end CountingMatroid.Analysis.InitialRestartLaw
namespace CountingMatroid.Interface
end CountingMatroid.Interface
namespace CountingMatroid.Analysis.TransversalRankBridge
end CountingMatroid.Analysis.TransversalRankBridge
namespace CountingMatroid.Analysis.GreedyRankCorrect
end CountingMatroid.Analysis.GreedyRankCorrect
section


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-!
Successful capped integer draws are characterized by their first accepted
word. The characterization records both the returned integer and the consumed
cursor, with all earlier fixed-width words rejected. Binary-word enumeration
counts the corresponding finite fair-bit cylinders exactly. Interval replay
then transfers fresh-suffix continuation bounds at each successful endpoint.
-/

namespace CountingMatroid.Analysis.BoundedUniformSuccessWords

open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.BoundedUniformAbortMass





/-- INTERNAL: Reading equal bit strings at possibly different cursor
positions gives equal binary values.
TEXLINE: main.tex:1392-1401 -/
theorem read_word_eq_of_bits (tape other : ℕ → Bool) (width value start otherStart : ℕ)
    (h : ∀ i < width, tape (start + i) = other (otherStart + i)) :
    (readWord tape width value start).1 = (readWord other width value otherStart).1 := by
  induction width generalizing value start otherStart with
  | zero => rfl
  | succ width ih =>
    have hb := h 0 (by omega)
    simp only [Nat.add_zero] at hb
    simp only [readWord, hb]
    apply ih
    intro i hi
    simpa only [Nat.add_assoc, Nat.add_comm 1 i] using h (i + 1) (by omega)



/-- INTERNAL: A complete fresh word has the uniform sum over its binary
values, with no dependence on the preceding history.
TEXLINE: main.tex:1392-1401 -/
theorem read_word_sum (width : ℕ) (F : ℕ → ℝ) :
    (∑ bits : List.Vector Bool width,
      F (readWord (FiniteStoppedFiberMass.finiteTape bits.val) width 0 0).1) =
      ∑ value : Fin (2 ^ width), F value.val := by
  exact Fintype.sum_bijective _ (read_word_bijective width) _ _ (fun _ => rfl)

/-- INTERNAL: A fresh word's binary value is unchanged by extending either
its previously consumed head or its later suffix.
TEXLINE: main.tex:1392-1401 -/
theorem read_word_after_prefix (head : List Bool) (width : ℕ)
    (bits : List.Vector Bool width) (tail : List Bool) :
    (readWord (FiniteStoppedFiberMass.finiteTape ((head ++ bits.val) ++ tail))
      width 0 head.length).1 =
      (readWord (FiniteStoppedFiberMass.finiteTape bits.val) width 0 0).1 := by
  apply read_word_eq_of_bits
  intro i hi
  unfold FiniteStoppedFiberMass.finiteTape
  rw [List.append_assoc, List.getElem?_append_right (by omega),
    Nat.add_sub_cancel_left, List.getElem?_append_left (by simpa only [bits.property] using hi)]
  simp only [Nat.zero_add]

















end CountingMatroid.Analysis.BoundedUniformSuccessWords

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* 2026-10-09 · proved · binary-word injectivity and finite-cardinality enumeration give the exact first-accepted-word cylinder mass. The sampler normal form identifies its stopping word uniquely, yielding the joint value/cursor law; successful interval replay and stopped_fiber_bound transfer a fresh-suffix continuation estimate. All declarations are proved.
-/

end
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-!
Successful capped integer draws are characterized by their first accepted
word. The characterization records both the returned integer and the consumed
cursor, with all earlier fixed-width words rejected. Binary-word enumeration
counts the corresponding finite fair-bit cylinders exactly. Interval replay
then transfers fresh-suffix continuation bounds at each successful endpoint.
-/

namespace CountingMatroid.Analysis.BoundedUniformSuccessWords
end CountingMatroid.Analysis.BoundedUniformSuccessWords
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.BoundedUniformSuccessWords

open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.BoundedUniformAbortMass

/-- INTERNAL: The first accepted word after k rejections has its exact
finite fair-suffix mass. No output uniformity is assumed in the proof.
TEXLINE: main.tex:1392-1401 -/
theorem solution (head : List Bool) (t width v k value : ℕ)
    (hw : 0 < width) (hv : v ≤ 2 ^ width) (ha : value < v)
    (hcover : (k + 1) * width ≤ t) :
    FiniteStoppedFiberMass.fairMass head t (fun tape =>
      (readWord tape width 0 (head.length + k * width)).1 = value ∧
      ∀ j < k, v ≤ (readWord tape width 0 (head.length + j * width)).1) =
      ((2 ^ width - v : ℕ) : ℝ) ^ k / (2 : ℝ) ^ ((k + 1) * width) := by
  classical
  induction k generalizing head t with
  | zero =>
    simp only [Nat.zero_mul, Nat.add_zero, Nat.zero_add, Nat.one_mul, pow_zero]
    rw [FiniteStoppedFiberMass.fairMass_split head t width (by omega)]
    have hconst (bits : List.Vector Bool width) :
        FiniteStoppedFiberMass.fairMass (head ++ bits.val) (t - width)
          (fun tape => (readWord tape width 0 head.length).1 = value ∧
            ∀ j < 0, v ≤ (readWord tape width 0 (head.length + j * width)).1) =
          if (readWord (FiniteStoppedFiberMass.finiteTape bits.val) width 0 0).1 = value
          then 1 else 0 := by
      unfold FiniteStoppedFiberMass.fairMass
      simp_rw [read_word_after_prefix head width bits]
      simp only [Nat.not_lt_zero, IsEmpty.forall_iff, forall_const, and_true]
      split_ifs <;> simp [card_vector]
    simp_rw [hconst, mul_ite, mul_one, mul_zero]
    rw [read_word_sum width (fun x => if x = value then 1 / (2 : ℝ) ^ width else 0)]
    let a : Fin (2 ^ width) := ⟨value, lt_of_lt_of_le ha hv⟩
    have heq (i : Fin (2 ^ width)) : i.val = value ↔ i = a := by
      exact ⟨fun h => Fin.ext h, fun h => congrArg Fin.val h⟩
    simp_rw [heq]
    simp
  | succ k ih =>
    rw [FiniteStoppedFiberMass.fairMass_split head t width (by nlinarith)]
    have hpart (bits : List.Vector Bool width) :
        FiniteStoppedFiberMass.fairMass (head ++ bits.val) (t - width)
          (fun tape => (readWord tape width 0 (head.length + (k + 1) * width)).1 = value ∧
            ∀ j < k + 1, v ≤ (readWord tape width 0 (head.length + j * width)).1) =
        (if v ≤ (readWord (FiniteStoppedFiberMass.finiteTape bits.val) width 0 0).1
          then (1 : ℝ) else 0) *
        FiniteStoppedFiberMass.fairMass (head ++ bits.val) (t - width)
          (fun tape => (readWord tape width 0 ((head ++ bits.val).length + k * width)).1 = value ∧
            ∀ j < k, v ≤ (readWord tape width 0 ((head ++ bits.val).length + j * width)).1) := by
      unfold FiniteStoppedFiberMass.fairMass
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro tail _
      let tape := FiniteStoppedFiberMass.finiteTape ((head ++ bits.val) ++ tail.val)
      have hlen : (head ++ bits.val).length = head.length + width := by simp
      have hhead : (readWord tape width 0 head.length).1 =
          (readWord (FiniteStoppedFiberMass.finiteTape bits.val) width 0 0).1 :=
        read_word_after_prefix head width bits tail.val
      have hoff (j : ℕ) : head.length + (j + 1) * width =
          (head ++ bits.val).length + j * width := by rw [hlen]; ring
      have hevent : ((readWord tape width 0 (head.length + (k + 1) * width)).1 = value ∧
          ∀ j < k + 1, v ≤ (readWord tape width 0 (head.length + j * width)).1) ↔
          v ≤ (readWord (FiniteStoppedFiberMass.finiteTape bits.val) width 0 0).1 ∧
          ((readWord tape width 0 ((head ++ bits.val).length + k * width)).1 = value ∧
          ∀ j < k, v ≤ (readWord tape width 0 ((head ++ bits.val).length + j * width)).1) := by
        rw [hoff k]
        constructor
        · rintro ⟨hval, hall⟩
          refine ⟨?_, hval, ?_⟩
          · simpa only [Nat.zero_mul, Nat.add_zero, hhead] using hall 0 (by omega)
          · intro j hj
            simpa only [hoff j] using hall (j + 1) (by omega)
        · rintro ⟨hfirst, hval, hall⟩
          refine ⟨hval, ?_⟩
          intro j hj
          cases j with
          | zero => simpa only [Nat.zero_mul, Nat.add_zero, hhead] using hfirst
          | succ j => simpa only [hoff j] using hall j (by omega)
      dsimp only [tape] at hevent
      simp +instances only [hevent, ite_and, ite_mul, one_mul, zero_mul]
      split_ifs <;> simp_all
      exfalso
      rename_i hfirst hvalue hbad hall
      obtain ⟨j, hj, hlt⟩ := hbad
      have hle := hall j hj
      omega
    have htailcover : (k + 1) * width ≤ t - width := by
      have hc : (k + 1) * width + width ≤ t := by nlinarith [hcover]
      omega
    simp_rw [hpart, ih (head ++ _) (t - width) htailcover]
    have hsum := read_word_rejected_sum width v hv
    have hfactor (x : ℝ) : (1 / (2 : ℝ) ^ width) *
        (x * (((2 ^ width - v : ℕ) : ℝ) ^ k / (2 : ℝ) ^ ((k + 1) * width))) =
        x * (((2 ^ width - v : ℕ) : ℝ) ^ k /
          ((2 : ℝ) ^ width * (2 : ℝ) ^ ((k + 1) * width))) := by ring
    simp_rw [hfactor]
    rw [← Finset.sum_mul, hsum]
    rw [← pow_add, show width + (k + 1) * width = (k + 1 + 1) * width by ring,
      pow_succ]
    ring
