-- Prove2me | solution 1 for CountingMatroid.Analysis.FiniteStoppedFiberMass.sum_split
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T15:06:25.024246+00:00
-- url     : https://prove2.me/submissions/789e5327-00db-4c16-b44a-4019d820bb29

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

namespace CountingMatroid.Meta
end CountingMatroid.Meta
namespace Arlib
end Arlib
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-! Finite uniform tape disintegration at a successful fixed endpoint cursor. -/
namespace CountingMatroid.Analysis.FiniteStoppedFiberMass
end CountingMatroid.Analysis.FiniteStoppedFiberMass
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.FiniteStoppedFiberMass

/-- INTERNAL: Split a finite uniform sum into its prefix and suffix sums. -/
theorem solution (t k : ℕ) (hk : k ≤ t) (f : List Bool → ℝ) :
    (∑ bits : List.Vector Bool t, f bits.val) =
      ∑ pref : List.Vector Bool k, ∑ tail : List.Vector Bool (t-k),
        f (pref.val ++ tail.val) := by
  classical
  let join : List.Vector Bool k × List.Vector Bool (t-k) → List.Vector Bool t :=
    fun p => ⟨p.1.val ++ p.2.val, by simp [Nat.add_sub_of_le hk]⟩
  have hj : Function.Bijective join := by
    constructor
    · intro a b heq
      have hv := congrArg Subtype.val heq
      have hp : a.1.val = b.1.val := by
        have h := congrArg (List.take k) hv
        simpa [join, List.take_append, a.1.2, b.1.2] using h
      have ht : a.2.val = b.2.val := by
        have h := congrArg (List.drop k) hv
        simpa [join, List.drop_append, a.1.2, b.1.2] using h
      exact Prod.ext (Subtype.ext hp) (Subtype.ext ht)
    · intro bits
      refine ⟨(⟨bits.val.take k, by simp [bits.2, Nat.min_eq_left hk]⟩,
        ⟨bits.val.drop k, by simp [bits.2]⟩), ?_⟩
      exact Subtype.ext (List.take_append_drop k bits.val)
  calc
    _ = ∑ p : List.Vector Bool k × List.Vector Bool (t-k), f (join p).val :=
      (Fintype.sum_bijective join hj _ _ (fun _ => rfl)).symm
    _ = _ := Fintype.sum_prod_type _
