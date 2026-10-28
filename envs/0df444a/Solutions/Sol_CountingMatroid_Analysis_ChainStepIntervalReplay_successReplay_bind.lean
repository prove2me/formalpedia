-- Prove2me | solution 1 for CountingMatroid.Analysis.ChainStepIntervalReplay.successReplay_bind
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T15:06:35.590402+00:00
-- url     : https://prove2.me/submissions/cf253a5b-183d-4b52-8ab2-0fea0fb3ec51

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
import Definitions.Def_CountingMatroid_Model_Operations
import Definitions.Def_CountingMatroid_Model_Prelude
import Definitions.Def_CountingMatroid_Model_Program
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

/-!
Success-path replay for the charged chain step. A successful transition has
a monotone cursor and depends only on its consumed bit interval. The generic
option-fold lemma also retains the program's absorbing abort state.
-/

namespace CountingMatroid.Analysis.ChainStepIntervalReplay
end CountingMatroid.Analysis.ChainStepIntervalReplay
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.ChainStepIntervalReplay
open CountingMatroid.Model CountingMatroid.Model.Operations CountingMatroid.Program
open CountingMatroid.Analysis.BoundedUniformReplay

/-- INTERNAL: Composition of two successful tape operations retains interval
replay; a successful composition cannot have aborted in its first operation. -/
theorem solution {α β : Type} (f : (ℕ → Bool) → Option α)
    (g : (ℕ → Bool) → α → Option β) (ca : α → ℕ) (cb : β → ℕ) (start : ℕ)
    (hf : SuccessReplay f ca start)
    (hg : ∀ a, SuccessReplay (fun tape => g tape a) cb (ca a)) :
    SuccessReplay (fun tape => (f tape).bind (g tape)) cb start := by
  intro tape out h
  cases hfirst : f tape with
  | none => simp +instances only [hfirst, Option.bind_none] at h; contradiction
  | some middle =>
    simp +instances only [hfirst, Option.bind_some] at h
    have ha := hf tape middle hfirst
    have hb := hg middle tape out h
    refine ⟨ha.1.trans hb.1, ?_⟩
    intro other hagree
    change (f other).bind (g other) = some out
    rw [ha.2 other (fun i hlo hhi => hagree i hlo (hhi.trans_le hb.1))]
    exact hb.2 other (fun i hlo hhi => hagree i (ha.1.trans hlo) hhi)
