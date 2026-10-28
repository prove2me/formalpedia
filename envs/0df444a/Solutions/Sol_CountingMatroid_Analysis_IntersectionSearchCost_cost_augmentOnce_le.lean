-- Prove2me | solution 1 for CountingMatroid.Analysis.IntersectionSearchCost.cost_augmentOnce_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T16:43:40.569983+00:00
-- url     : https://prove2.me/submissions/21a0ca70-18ee-45ab-91ba-5f76922c78f4

import Definitions.Def_CountingMatroidSupport_Computation_Charged
import Definitions.Def_CountingMatroidSupport_Computation_Charged_Extension1
import Definitions.Def_CountingMatroidSupport_Computation_Charged_Extension2
import Definitions.Def_CountingMatroidSupport_Computation_Cost
import Definitions.Def_CountingMatroidSupport_Computation_Cost_Extension1
import Definitions.Def_CountingMatroidSupport_Computation_Machine
import Definitions.Def_CountingMatroidSupport_Computation_Machine_Extension1
import Definitions.Def_CountingMatroidSupport_Computation_Space
import Definitions.Def_CountingMatroid_Analysis_IntersectionSearch
import Definitions.Def_CountingMatroid_Model_Operations
import Definitions.Def_CountingMatroid_Model_Prelude
import Definitions.Def_CountingMatroid_Model_Subroutines
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Combinatorics.Matroid.Rank.ENat
import Mathlib.Data.BitVec
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Ring.RingNF
import Theorems.Thm_CountingMatroid_Analysis_IntersectionSearchCost_cost_buildGraph_le
import Theorems.Thm_CountingMatroid_Analysis_IntersectionSearchCost_cost_findPath_le

namespace CountingMatroid.Analysis.IntersectionSearchCost
end CountingMatroid.Analysis.IntersectionSearchCost
namespace Arlib
end Arlib
section


set_option autoImplicit false

/-!
Uniform resource obligation for the concrete capped exchange-graph solver.
The proved bound composes table and fold accounting through graph construction,
frozen breadth-first layers, sink selection, and at most `n` toggles, then
through the `r`-round solver.
It is independent of all matroid and exact-oracle promises.
-/

namespace CountingMatroid.Analysis.IntersectionSearchCost

open CountingMatroid.Model CountingMatroid.Model.Operations
open CountingMatroid.Model.Subroutines
open CountingMatroid.Analysis.IntersectionSearch



/-- INTERNAL: A uniform coordinate bound on each body controls a charged fold. -/
theorem cost_foldl_le {α β : Type} (f : β → α → Arlib.Computation.Charged Op Cell β)
    (l : List α) (k : ℕ) (hf : ∀ b a op, (f b a).cost op ≤ k)
    (b : β) (op : Op) :
    (Arlib.Computation.Charged.foldl f l b).cost op ≤ l.length * k := by
  induction l generalizing b with
  | nil => simp
  | cons a l ih =>
    rw [Arlib.Computation.Charged.cost_foldl_cons]
    simp only [Pi.add_apply, List.length_cons]
    have hhead := hf b a op
    have htail := ih (f b a).val
    nlinarith













/-- INTERNAL: Toggling an element pays membership and one bounded update. -/
theorem cost_toggle_le {n : ℕ} (I : Finset (Fin n)) (i : Fin n) (op : Op) :
    (toggle I i).cost op ≤ 2 * (n + 1) := by
  by_cases hi : i ∈ I <;>
    simp [toggle, containsElement, insertElement, hi,
      Arlib.Computation.CostVec.one, Arlib.Computation.CostVec.many] <;>
    split_ifs <;> omega













end CountingMatroid.Analysis.IntersectionSearchCost

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r16 · proved · closed the unconditional cost certificate by coordinate bounds through table construction, capped search, toggles, and the rank-many loop; no oracle promise is used.
-/

end
set_option autoImplicit false

/-!
Uniform resource obligation for the concrete capped exchange-graph solver.
The proved bound composes table and fold accounting through graph construction,
frozen breadth-first layers, sink selection, and at most `n` toggles, then
through the `r`-round solver.
It is independent of all matroid and exact-oracle promises.
-/

namespace CountingMatroid.Analysis.IntersectionSearchCost
end CountingMatroid.Analysis.IntersectionSearchCost
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.IntersectionSearchCost

open CountingMatroid.Model CountingMatroid.Model.Operations
open CountingMatroid.Model.Subroutines
open CountingMatroid.Analysis.IntersectionSearch

/-- INTERNAL: One augmentation builds a graph, searches it, and toggles
at most `n` elements; its bound needs no oracle correctness hypothesis. -/
theorem solution {n : ℕ} (o₁ o₂ : IndependenceOracle n)
    (I : Finset (Fin n)) (op : Op) :
    (augmentOnce o₁ o₂ I).cost op ≤ 60 * (n + 1) ^ 5 := by
  have hgraph := cost_buildGraph_le o₁ o₂ I op
  have hpath := cost_findPath_le (buildGraph o₁ o₂ I).val op
  have htoggle (p : List (Fin n)) := cost_foldl_le toggle (p.take n)
    (2 * (n + 1)) (fun I i op => cost_toggle_le I i op) I op
  have htoggle' (p : List (Fin n)) :
      (Arlib.Computation.Charged.foldl toggle (p.take n) I).cost op ≤
        n * (2 * (n + 1)) :=
    (htoggle p).trans (Nat.mul_le_mul_right _ (List.length_take_le n p))
  have h45 : (n + 1) ^ 4 ≤ (n + 1) ^ 5 :=
    pow_le_pow_right₀ (by omega) (by omega)
  have htoggleSize : n * (2 * (n + 1)) ≤ 2 * (n + 1) ^ 5 := by
    calc
      _ = 2 * (n * (n + 1)) := by ring
      _ ≤ 2 * ((n + 1) * (n + 1)) := by gcongr; omega
      _ = 2 * (n + 1) ^ 2 := by ring
      _ ≤ 2 * (n + 1) ^ 5 := Nat.mul_le_mul_left 2
        (pow_le_pow_right₀ (by omega) (by omega))
  unfold augmentOnce
  simp only [Arlib.Computation.Charged.cost_bind, Pi.add_apply]
  cases hp : (findPath (buildGraph o₁ o₂ I).val).val with
  | none =>
    simp only [Arlib.Computation.Charged.cost_pure, Pi.zero_apply, Nat.add_zero]
    exact (Nat.add_le_add hgraph hpath).trans (by nlinarith)
  | some p =>
    exact (Nat.add_le_add hgraph (Nat.add_le_add hpath (htoggle' p))).trans
      (by nlinarith)
