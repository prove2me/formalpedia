-- Prove2me | solution 1 for CountingMatroid.Analysis.FiniteStoppedFiberMass.stopped_fiber_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T15:57:04.111995+00:00
-- url     : https://prove2.me/submissions/2d9bc9e6-3a71-481e-bb41-2471d25dd25c

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
import Definitions.Def_CountingMatroid_Analysis_ChainStepIntervalReplay
import Definitions.Def_CountingMatroid_Analysis_FiniteStoppedFiberMass
import Definitions.Def_CountingMatroid_Model_Operations
import Definitions.Def_CountingMatroid_Model_Prelude
import Definitions.Def_CountingMatroid_Model_Program
import Definitions.Def_CountingMatroid_Model_Subroutines
import Lean
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
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
import Mathlib.Data.Fintype.Vector
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Sort
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Order.Interval.Set.Basic
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
import Theorems.Thm_CountingMatroid_Analysis_FiniteStoppedFiberMass_fairMass_split

namespace CountingMatroid.Meta
end CountingMatroid.Meta
namespace Arlib
end Arlib
section


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-! Finite uniform tape disintegration at a successful fixed endpoint cursor. -/
namespace CountingMatroid.Analysis.FiniteStoppedFiberMass









/-- INTERNAL: Appending fresh bits leaves every bit in the old prefix fixed. -/
theorem finiteTape_append_agree (head tail₁ tail₂ : List Bool) (i : ℕ)
    (hi : i < head.length) :
    finiteTape (head ++ tail₁) i = finiteTape (head ++ tail₂) i := by
  unfold finiteTape
  rw [List.getElem?_append_left hi, List.getElem?_append_left hi]











end CountingMatroid.Analysis.FiniteStoppedFiberMass

end
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-! Finite uniform tape disintegration at a successful fixed endpoint cursor. -/
namespace CountingMatroid.Analysis.FiniteStoppedFiberMass
end CountingMatroid.Analysis.FiniteStoppedFiberMass
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.FiniteStoppedFiberMass

/-- INTERNAL: Successful fixed-endpoint fibers are cylinders at their ending
cursor, so a uniform continuation bound multiplies the unnormalised fiber mass.
TEXLINE: main.tex:1207-1212,1392-1421 -/
theorem solution {α : Type} (head : List Bool) (t : ℕ)
    (f : (ℕ → Bool) → Option α) (cursor : α → ℕ)
    (hf : ChainStepIntervalReplay.SuccessReplay f cursor head.length)
    (a : α) (ha : head.length ≤ cursor a) (hc : cursor a ≤ head.length + t)
    (E : (ℕ → Bool) → Prop) (B : ℝ) (hB : 0 ≤ B)
    (hcont : ∀ pref : List.Vector Bool (cursor a - head.length),
      f (finiteTape (head ++ pref.val)) = some a →
      fairMass (head ++ pref.val) (t - (cursor a - head.length)) E ≤ B) :
    fairMass head t (fun tape => f tape = some a ∧ E tape) ≤
      fairMass head t (fun tape => f tape = some a) * B := by
  classical
  let k := cursor a - head.length
  have hk : k ≤ t := by dsimp [k]; omega
  have hlen (pref : List.Vector Bool k) : (head ++ pref.val).length = cursor a := by
    simp only [List.length_append, pref.2]
    dsimp [k]
    omega
  have hfiber (pref : List.Vector Bool k) (tail : List Bool) :
      f (finiteTape ((head ++ pref.val) ++ tail)) = some a ↔
        f (finiteTape (head ++ pref.val)) = some a := by
    have hagree : ∀ i, i < cursor a →
        finiteTape ((head ++ pref.val) ++ tail) i = finiteTape (head ++ pref.val) i := by
      intro i hi
      simpa only [List.append_nil] using
        finiteTape_append_agree (head ++ pref.val) tail [] i (by rw [hlen]; exact hi)
    constructor <;> intro h
    · exact (hf _ a h).2 _ (fun i _ hi => hagree i hi)
    · exact (hf _ a h).2 _ (fun i _ hi => (hagree i hi).symm)
  rw [fairMass_split head t k hk, fairMass_split head t k hk, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro pref _
  by_cases hinit : f (finiteTape (head ++ pref.val)) = some a
  · have hleft : fairMass (head ++ pref.val) (t-k)
        (fun tape => f tape = some a ∧ E tape) = fairMass (head ++ pref.val) (t-k) E := by
      unfold fairMass
      apply Finset.sum_congr rfl
      intro tail _
      simp +instances only [hfiber pref tail.val, hinit, true_and]
    have hright : fairMass (head ++ pref.val) (t-k)
        (fun tape => f tape = some a) = 1 := by
      unfold fairMass
      simp_rw [hfiber, hinit, if_true]
      simp [card_vector]
    rw [hleft, hright, mul_one]
    exact mul_le_mul_of_nonneg_left (hcont pref hinit) (by positivity)
  · have hz : fairMass (head ++ pref.val) (t-k)
        (fun tape => f tape = some a) = 0 := by
      unfold fairMass
      simp_rw [hfiber, hinit, if_false]
      simp
    have hz' : fairMass (head ++ pref.val) (t-k)
        (fun tape => f tape = some a ∧ E tape) = 0 := by
      unfold fairMass
      simp_rw [hfiber, hinit, false_and, if_false]
      simp
    rw [hz, hz']
    simp
