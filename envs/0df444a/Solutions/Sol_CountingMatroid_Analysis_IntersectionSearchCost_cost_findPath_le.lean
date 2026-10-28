-- Prove2me | solution 1 for CountingMatroid.Analysis.IntersectionSearchCost.cost_findPath_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T16:41:16.796686+00:00
-- url     : https://prove2.me/submissions/43ffa847-632e-4389-b977-58825f2e34e8

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
import Theorems.Thm_CountingMatroid_Analysis_IntersectionSearchCost_cost_initialPaths_le
import Theorems.Thm_CountingMatroid_Analysis_IntersectionSearchCost_cost_tabulate_le

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







/-- INTERNAL: A predecessor scan either retains a found path or pays for
one bounded path-table read, edge read, and capped path write. -/
theorem cost_predecessorStep_le {n : ℕ} (g : ExchangeGraph n) (previous : Paths n)
    (v : Fin n) (found : Option (List (Fin n))) (u : Fin n) (op : Op) :
    (predecessorStep g previous v found u).cost op ≤
      n * (n + 1) + n * n + n + 4 := by
  cases found <;> cases hp : previous u <;> cases he : g.edges u v <;>
    simp [predecessorStep, isSome, hp, he,
      Arlib.Computation.CostVec.one, Arlib.Computation.CostVec.many] <;>
    split_ifs <;> omega

/-- INTERNAL: A vertex relaxation scans at most `n` predecessors. -/
theorem cost_relaxVertex_le {n : ℕ} (g : ExchangeGraph n) (previous : Paths n)
    (v : Fin n) (op : Op) :
    (relaxVertex g previous v).cost op ≤
      n * (n + 1) + 2 + n * (n * (n + 1) + n * n + n + 4) := by
  have hfold := cost_foldl_le (predecessorStep g previous v) (List.finRange n)
    (n * (n + 1) + n * n + n + 4)
    (fun found u op => cost_predecessorStep_le g previous v found u op) none op
  simp only [List.length_finRange] at hfold
  cases hp : previous v <;>
    simp [relaxVertex, isSome, hp,
      Arlib.Computation.CostVec.one, Arlib.Computation.CostVec.many] <;>
    split_ifs <;> omega

/-- INTERNAL: Sink selection charges its bounded table and length scans. -/
theorem cost_sinkStep_le {n : ℕ} (g : ExchangeGraph n) (paths : Paths n)
    (best : Option (List (Fin n))) (i : Fin n) (op : Op) :
    (sinkStep g paths best i).cost op ≤ n * (n + 1) + 5 * n + 6 := by
  cases ht : (g.terminals i).2 <;> cases hp : paths i <;> cases best <;>
    simp [sinkStep, lessThan, ht, hp,
      Arlib.Computation.CostVec.one, Arlib.Computation.CostVec.many] <;>
    split_ifs <;> (try simp only [Arlib.Computation.Charged.cost_pure, Pi.zero_apply]) <;> omega







/-- INTERNAL: One frozen breadth-first layer has a quartic coordinate bound. -/
theorem cost_relaxPaths_le {n : ℕ} (g : ExchangeGraph n) (previous : Paths n)
    (op : Op) : (relaxPaths g previous).cost op ≤ 10 * (n + 1) ^ 4 := by
  have h := cost_tabulate_le (n + 1)
    (n * (n + 1) + 2 + n * (n * (n + 1) + n * n + n + 4))
    (relaxVertex g previous) (fun v op => cost_relaxVertex_le g previous v op) op
  exact h.trans (by nlinarith)







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

/-- INTERNAL: Capped breadth-first search and shortest sink selection cost
at most a fixed quintic polynomial, regardless of the graph's origin. -/
theorem solution {n : ℕ} (g : ExchangeGraph n) (op : Op) :
    (findPath g).cost op ≤ 30 * (n + 1) ^ 5 := by
  have hinit := cost_initialPaths_le g op
  have hlayers (paths : Paths n) := cost_foldl_le
    (fun paths (_ : ℕ) => relaxPaths g paths) (List.range n)
    (10 * (n + 1) ^ 4) (fun paths _ op => cost_relaxPaths_le g paths op) paths op
  have hsinks (paths : Paths n) := cost_foldl_le (sinkStep g paths) (List.finRange n)
    (n * (n + 1) + 5 * n + 6)
    (fun best i op => cost_sinkStep_le g paths best i op) none op
  simp only [List.length_range] at hlayers
  simp only [List.length_finRange] at hsinks
  have h35 : (n + 1) ^ 3 ≤ (n + 1) ^ 5 :=
    pow_le_pow_right₀ (by omega) (by omega)
  have hlayerSize : n * (10 * (n + 1) ^ 4) ≤ 10 * (n + 1) ^ 5 := by
    calc
      _ = 10 * (n * (n + 1) ^ 4) := by ring
      _ ≤ 10 * ((n + 1) * (n + 1) ^ 4) := by gcongr; omega
      _ = 10 * (n + 1) ^ 5 := by ring
  have hsinkSize : n * (n * (n + 1) + 5 * n + 6) ≤ 10 * (n + 1) ^ 3 := by
    nlinarith
  unfold findPath
  simp only [Arlib.Computation.Charged.cost_bind, Pi.add_apply]
  calc
    _ ≤ 10 * (n + 1) ^ 3 +
        (n * (10 * (n + 1) ^ 4) + n * (n * (n + 1) + 5 * n + 6)) :=
      Nat.add_le_add hinit (Nat.add_le_add (hlayers _) (hsinks _))
    _ ≤ 30 * (n + 1) ^ 5 := by nlinarith
