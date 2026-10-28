-- Prove2me | solution 1 for CountingMatroid.Analysis.IntersectionSearchCost.cost_buildGraph_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T16:08:29.488141+00:00
-- url     : https://prove2.me/submissions/dbc0b871-a0f9-4421-b026-7a733fce1ea7

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







/-- INTERNAL: Uniform coordinate bound for the charged insertion tests. -/
theorem cost_testTerminal_le {n : ℕ} (o₁ o₂ : IndependenceOracle n)
    (I : Finset (Fin n)) (i : Fin n) (op : Op) :
    (testTerminal o₁ o₂ I i).cost op ≤ n * (n + 1) + n + 6 := by
  simp [testTerminal, containsElement, insertElement, encodeQuery, oracleQuery,
    Arlib.Computation.CostVec.one, Arlib.Computation.CostVec.many]
  split_ifs <;> omega

/-- INTERNAL: Uniform coordinate bound for both oriented exchange tests. -/
theorem cost_testEdge_le {n : ℕ} (o₁ o₂ : IndependenceOracle n)
    (I : Finset (Fin n)) (u v : Fin n) (op : Op) :
    (testEdge o₁ o₂ I u v).cost op ≤ 2 * (n * (n + 1)) + 4 * (n + 1) + 9 := by
  simp [testEdge, containsElement, insertElement, encodeQuery, oracleQuery,
    Arlib.Computation.CostVec.one, Arlib.Computation.CostVec.many]
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

/-- INTERNAL: Graph construction has a uniform quartic coordinate bound. -/
theorem solution {n : ℕ} (o₁ o₂ : IndependenceOracle n)
    (I : Finset (Fin n)) (op : Op) :
    (buildGraph o₁ o₂ I).cost op ≤ 20 * (n + 1) ^ 4 := by
  have ht := cost_tabulate_le 2 (n * (n + 1) + n + 6)
    (testTerminal o₁ o₂ I) (fun i op => cost_testTerminal_le o₁ o₂ I i op) op
  have hr (u : Fin n) (op : Op) := cost_tabulate_le 1
    (2 * (n * (n + 1)) + 4 * (n + 1) + 9) (testEdge o₁ o₂ I u)
    (fun v op => cost_testEdge_le o₁ o₂ I u v op) op
  have he := cost_tabulate_le (n + 1)
    ((n * 1 + 1) + n * ((2 * (n * (n + 1)) + 4 * (n + 1) + 9) + (n * 1 + 1)))
    (fun u => tabulate 1 (testEdge o₁ o₂ I u)) hr op
  simp only [buildGraph, Arlib.Computation.Charged.cost_bind, Pi.add_apply,
    Arlib.Computation.Charged.cost_pure, Pi.zero_apply, Nat.add_zero]
  exact (Nat.add_le_add ht he).trans (by nlinarith)
