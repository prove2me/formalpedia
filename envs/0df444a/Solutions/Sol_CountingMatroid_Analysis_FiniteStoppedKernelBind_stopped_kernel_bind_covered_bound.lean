-- Prove2me | solution 1 for CountingMatroid.Analysis.FiniteStoppedKernelBind.stopped_kernel_bind_covered_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T16:15:06.399986+00:00
-- url     : https://prove2.me/submissions/43dba655-830b-4640-a7ec-79c1a070f779

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
import Theorems.Thm_CountingMatroid_Analysis_FiniteStoppedKernelBind_stopped_kernel_bind_bound

namespace CountingMatroid.Analysis.FiniteStoppedKernelBind
end CountingMatroid.Analysis.FiniteStoppedKernelBind
namespace CountingMatroid.Meta
end CountingMatroid.Meta
namespace Arlib
end Arlib
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-! A finite stopped operation can be followed by a uniformly bounded fresh
continuation without conditioning away its abort mass. -/
namespace CountingMatroid.Analysis.FiniteStoppedKernelBind
end CountingMatroid.Analysis.FiniteStoppedKernelBind
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.FiniteStoppedKernelBind
open CountingMatroid.Analysis.FiniteStoppedFiberMass

/-- INTERNAL: The stopped-bind comparison with a finite state marginal and
an explicit coverage restriction on the initializer's ending cursor.
TEXLINE: main.tex:1163-1176,1392-1421 -/
theorem solution {α Ω : Type} [Fintype Ω]
    (head : List Bool) (t : ℕ) (f : (ℕ → Bool) → Option α)
    (cursor : α → ℕ) (state : α → Ω)
    (hf : ChainStepIntervalReplay.SuccessReplay f cursor head.length)
    (E : (ℕ → Bool) → α → Prop) (B : Ω → ℝ) (hB : ∀ x, 0 ≤ B x)
    (hcovered : ∀ bits : List.Vector Bool t, ∀ a,
      f (finiteTape (head ++ bits.val)) = some a →
      E (finiteTape (head ++ bits.val)) a → cursor a ≤ head.length + t)
    (hcont : ∀ a, head.length ≤ cursor a → cursor a ≤ head.length + t →
      ∀ pref : List.Vector Bool (cursor a - head.length),
      f (finiteTape (head ++ pref.val)) = some a →
      fairMass (head ++ pref.val) (t - (cursor a - head.length))
        (fun tape => E tape a) ≤ B (state a)) :
    fairMass head t (fun tape => ∃ a, f tape = some a ∧ E tape a) ≤
      ∑ x : Ω, fairMass head t (fun tape => ∃ a, f tape = some a ∧
        cursor a ≤ head.length + t ∧ state a = x) * B x := by
  classical
  let C := fun a => if cursor a ≤ head.length + t then B (state a) else 0
  have hbound := stopped_kernel_bind_bound head t f cursor hf E C
    (fun a => by dsimp only [C]; split_ifs <;> [exact hB _; exact le_rfl])
    hcovered (by
      intro a ha hc pref hf
      simpa only [C, hc, if_true] using hcont a ha hc pref hf)
  apply hbound.trans_eq
  unfold fairMass
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro bits _
  have hterm (R : Option α) : (1 / (2 : ℝ)^t) * (R.map C).getD 0 =
      ∑ x : Ω, (if ∃ a, R = some a ∧ cursor a ≤ head.length+t ∧ state a = x
        then 1 / (2 : ℝ)^t else 0) * B x := by
    cases R with
    | none => simp only [Option.map_none, Option.getD_none, mul_zero,
        reduceCtorEq, false_and, exists_false, if_false, zero_mul, Finset.sum_const_zero]
    | some a =>
      simp only [Option.map_some, Option.getD_some, Option.some.injEq, exists_eq_left']
      by_cases hc : cursor a ≤ head.length + t
      · simp +instances only [exists_eq_left', hc, true_and, C, if_true, ite_mul, zero_mul,
          Finset.sum_ite_eq, Finset.mem_univ, if_true]
      · simp +instances only [exists_eq_left', hc, false_and, C, if_false, mul_zero,
          zero_mul, Finset.sum_const_zero]
  convert hterm (f (finiteTape (head ++ bits.val))) using 1
  apply Finset.sum_congr rfl
  intro x _
  split_ifs <;> rfl
